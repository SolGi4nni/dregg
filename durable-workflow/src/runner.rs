//! `runner` — the pluggable step-executor seam.
//!
//! The durable workflow engine coordinates *when* steps run, checkpoints their
//! results, and meters them exactly-once — but it does not care *what* a step
//! does. That is the [`StepRunner`] seam: one method, [`StepRunner::run`], that
//! takes a [`WorkloadSpec`] and returns its value. The engine holds a
//! `Arc<dyn StepRunner>` and calls it inside each durable `RunWorkload` activity.
//!
//! This is deliberately substrate-general. A production deployment plugs in a
//! runner that drives a real isolate — a wasm sandbox, an OCI container, a
//! microVM — behind this same trait; the checkpoint / resume / meter machinery is
//! unchanged. The bundled [`ExprRunner`] is a small deterministic interpreter so
//! the engine is complete and testable on its own, with no external executor.
//!
//! A runner MUST be **deterministic** in the sense durable execution requires: a
//! given `spec` produces the same value on the original run and on any replay.
//! (Nondeterministic effects belong *inside* a step whose recorded output is then
//! replayed, never in the coordination that decides which step runs next.)

use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// One workload step: an opaque, runner-interpreted unit of work.
///
/// `label` identifies the step in the durable history and the meter ledger (e.g.
/// `"build"`). `lang` selects how the [`StepRunner`] interprets `source` (for the
/// bundled [`ExprRunner`]: `"expr"` | `"echo"` | `"const"`; a wasm runner would
/// use `"wat"` / `"wasm"`). `tier` is an opaque capability grade a runner MAY use
/// to pick an isolation level — the engine passes it through untouched.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct WorkloadSpec {
    pub label: String,
    pub lang: String,
    pub source: String,
    #[serde(default)]
    pub tier: String,
}

impl WorkloadSpec {
    /// A step run by the bundled [`ExprRunner`]'s `expr` mini-language.
    pub fn expr(label: impl Into<String>, source: impl Into<String>) -> WorkloadSpec {
        WorkloadSpec {
            label: label.into(),
            lang: "expr".to_string(),
            source: source.into(),
            tier: String::new(),
        }
    }

    /// A step that echoes its `source` verbatim (the identity step).
    pub fn echo(label: impl Into<String>, source: impl Into<String>) -> WorkloadSpec {
        WorkloadSpec {
            label: label.into(),
            lang: "echo".to_string(),
            source: source.into(),
            tier: String::new(),
        }
    }
}

/// The step-executor seam. One method: run a step, return its value (or an error
/// string that fails the durable workflow). Held by the engine as
/// `Arc<dyn StepRunner>` and invoked inside each checkpointed `RunWorkload`
/// activity, so the value returned here is exactly what a crash-resume replays.
pub trait StepRunner: Send + Sync + 'static {
    /// Run one step. MUST be deterministic: the same `spec` yields the same value
    /// on the first run and on every replay (that is what makes the recorded
    /// result a faithful stand-in for re-execution).
    fn run(&self, spec: &WorkloadSpec) -> Result<String, String>;
}

impl<T: StepRunner + ?Sized> StepRunner for Arc<T> {
    fn run(&self, spec: &WorkloadSpec) -> Result<String, String> {
        (**self).run(spec)
    }
}

/// The bundled deterministic runner: enough of a step language to exercise the
/// engine end-to-end (a real dependency chain, `Err` on bad input) with no
/// external executor. It is NOT a general compute sandbox — a production runner
/// implements [`StepRunner`] over a real isolate.
///
/// Languages:
/// - `"echo"` / `"const"` — return `source` (trimmed) verbatim.
/// - `"expr"` — evaluate `source` as one integer arithmetic expression:
///   an integer literal, or `A <op> B` with `op ∈ {+, -, *}` and integer `A`, `B`.
///   Returns the integer as a decimal string. Overflow / malformed input is `Err`.
#[derive(Debug, Clone, Default)]
pub struct ExprRunner;

impl StepRunner for ExprRunner {
    fn run(&self, spec: &WorkloadSpec) -> Result<String, String> {
        match spec.lang.as_str() {
            "echo" | "const" => Ok(spec.source.trim().to_string()),
            "expr" => eval_expr(&spec.source).map(|v| v.to_string()),
            other => Err(format!(
                "step `{}`: ExprRunner cannot run lang `{other}` \
                 (plug in a StepRunner that can)",
                spec.label
            )),
        }
    }
}

/// Evaluate a single `A op B` (or bare integer) expression over `i64`.
fn eval_expr(src: &str) -> Result<i64, String> {
    let s = src.trim();
    if let Ok(v) = s.parse::<i64>() {
        return Ok(v);
    }
    // Find a binary operator that is not the leading sign of `A`.
    for (i, c) in s.char_indices() {
        if i == 0 {
            continue;
        }
        if matches!(c, '+' | '-' | '*') {
            let (lhs, rest) = s.split_at(i);
            let rhs = &rest[1..];
            let a: i64 = lhs
                .trim()
                .parse()
                .map_err(|_| format!("expr: bad left operand in `{s}`"))?;
            let b: i64 = rhs
                .trim()
                .parse()
                .map_err(|_| format!("expr: bad right operand in `{s}`"))?;
            let out = match c {
                '+' => a.checked_add(b),
                '-' => a.checked_sub(b),
                '*' => a.checked_mul(b),
                _ => unreachable!(),
            };
            return out.ok_or_else(|| format!("expr: overflow evaluating `{s}`"));
        }
    }
    Err(format!("expr: not a recognized expression: `{s}`"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expr_runner_evaluates_chain() {
        let r = ExprRunner;
        assert_eq!(r.run(&WorkloadSpec::expr("s1", "40 + 2")).unwrap(), "42");
        assert_eq!(r.run(&WorkloadSpec::expr("s2", "42 * 2")).unwrap(), "84");
        assert_eq!(r.run(&WorkloadSpec::expr("s3", "-5 + 8")).unwrap(), "3");
        assert_eq!(r.run(&WorkloadSpec::echo("s4", "  hi ")).unwrap(), "hi");
    }

    #[test]
    fn expr_runner_rejects_bad_input() {
        let r = ExprRunner;
        assert!(r.run(&WorkloadSpec::expr("s", "not math")).is_err());
        assert!(r
            .run(&WorkloadSpec {
                label: "s".into(),
                lang: "wasm".into(),
                source: String::new(),
                tier: String::new(),
            })
            .is_err());
    }
}
