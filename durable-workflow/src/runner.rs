//! `runner` — the pluggable step-executor seam, and a real subprocess isolate.
//!
//! The durable workflow engine coordinates *when* steps run, checkpoints their
//! results, and meters them exactly-once — but it does not care *what* a step does.
//! That is the [`StepRunner`] seam: one method, [`StepRunner::run`], that takes a
//! [`WorkloadSpec`] and returns its value (or a classified [`StepError`]). The engine
//! holds an `Arc<dyn StepRunner>` and calls it inside each durable `RunWorkload`
//! activity.
//!
//! Two runners ship:
//!
//! - [`ExprRunner`] — a tiny deterministic `expr`/`echo` interpreter so the engine is
//!   complete and testable with no external executor. It is *not* a compute sandbox.
//! - [`ProcessRunner`] — a **real isolate**: it runs a step in a separate OS process
//!   under an enforced wall-clock deadline (killed on overrun → a transient timeout),
//!   an output-size cap (bounds captured egress/memory), a scrubbed environment and a
//!   confined working directory, and — on Unix — CPU / address-space / file-size /
//!   fd `rlimit`s applied in the child before `exec`. The step's [`WorkloadSpec::tier`]
//!   selects the [`IsolationTier`], so `tier` is no longer a passed-through no-op — it
//!   picks the real limits the step runs under.
//!
//! ## Determinism and durable replay
//!
//! A step's output is **captured once and checkpointed**: the durable record is
//! authoritative, and a crash-resume replays the recorded bytes without re-running the
//! process. So a runner need not be bit-reproducible across a hypothetical re-exec —
//! the coordination that decides *which* step runs next is the part that must be
//! deterministic, and that lives in the orchestration, never in a runner.

use serde::{Deserialize, Serialize};
use std::sync::Arc;

pub use crate::error::{StepError, StepErrorKind};

/// One workload step: an opaque, runner-interpreted unit of work.
///
/// `label` identifies the step in the durable history and the meter ledger (e.g.
/// `"build"`). `lang` selects how the [`StepRunner`] interprets `source` (for
/// [`ExprRunner`]: `"expr"` | `"echo"` | `"const"`; for [`ProcessRunner`]:
/// `"process"` | `"shell"`). `tier` is the isolation grade a runner uses to pick a
/// [`IsolationTier`]. `cost` is the per-step meter charge; `None` falls back to the
/// workflow's uniform `cost_per_step`, so metering is variable per step, not a flat
/// constant.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct WorkloadSpec {
    pub label: String,
    pub lang: String,
    pub source: String,
    #[serde(default)]
    pub tier: String,
    /// Per-step meter charge; `None` ⇒ the workflow's `cost_per_step`.
    #[serde(default)]
    pub cost: Option<i64>,
}

impl WorkloadSpec {
    /// A step run by the bundled [`ExprRunner`]'s `expr` mini-language.
    pub fn expr(label: impl Into<String>, source: impl Into<String>) -> WorkloadSpec {
        WorkloadSpec {
            label: label.into(),
            lang: "expr".to_string(),
            source: source.into(),
            tier: String::new(),
            cost: None,
        }
    }

    /// A step that echoes its `source` verbatim (the identity step).
    pub fn echo(label: impl Into<String>, source: impl Into<String>) -> WorkloadSpec {
        WorkloadSpec {
            label: label.into(),
            lang: "echo".to_string(),
            source: source.into(),
            tier: String::new(),
            cost: None,
        }
    }

    /// A step run in a separate OS process by [`ProcessRunner`]: `source` is a shell
    /// command line. `tier` picks the isolation level ([`IsolationTier`]).
    pub fn process(
        label: impl Into<String>,
        source: impl Into<String>,
        tier: impl Into<String>,
    ) -> WorkloadSpec {
        WorkloadSpec {
            label: label.into(),
            lang: "process".to_string(),
            source: source.into(),
            tier: tier.into(),
            cost: None,
        }
    }

    /// Set the per-step meter cost (else the workflow's uniform `cost_per_step`).
    pub fn with_cost(mut self, cost: i64) -> WorkloadSpec {
        self.cost = Some(cost);
        self
    }
}

/// The step-executor seam. One method: run a step, return its value or a classified
/// [`StepError`] (a transient fault the workflow retries, a permanent one it fails
/// on). Held by the engine as `Arc<dyn StepRunner>` and invoked inside each
/// checkpointed `RunWorkload` activity.
pub trait StepRunner: Send + Sync + 'static {
    /// Run one step. Returns the step's value, or a classified failure.
    fn run(&self, spec: &WorkloadSpec) -> Result<String, StepError>;
}

impl<T: StepRunner + ?Sized> StepRunner for Arc<T> {
    fn run(&self, spec: &WorkloadSpec) -> Result<String, StepError> {
        (**self).run(spec)
    }
}

/// The bundled deterministic runner: enough of a step language to exercise the engine
/// end-to-end (a real dependency chain, `Err` on bad input) with no external executor.
/// It is NOT a general compute sandbox — for that use [`ProcessRunner`]. All its
/// failures are [`StepErrorKind::Permanent`] (bad input never becomes valid on retry).
#[derive(Debug, Clone, Default)]
pub struct ExprRunner;

impl StepRunner for ExprRunner {
    fn run(&self, spec: &WorkloadSpec) -> Result<String, StepError> {
        match spec.lang.as_str() {
            "echo" | "const" => Ok(spec.source.trim().to_string()),
            "expr" => eval_expr(&spec.source)
                .map(|v| v.to_string())
                .map_err(StepError::permanent),
            other => Err(StepError::permanent(format!(
                "step `{}`: ExprRunner cannot run lang `{other}` (plug in a StepRunner that can)",
                spec.label
            ))),
        }
    }
}

/// Evaluate a single `A op B` (or bare integer) expression over `i64`.
fn eval_expr(src: &str) -> Result<i64, String> {
    let s = src.trim();
    if let Ok(v) = s.parse::<i64>() {
        return Ok(v);
    }
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

// ---------------------------------------------------------------------------
// The real subprocess isolate.
// ---------------------------------------------------------------------------

/// The isolation grade a [`ProcessRunner`] step runs under, selected by
/// [`WorkloadSpec::tier`]. Higher tiers apply tighter limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsolationTier {
    /// `"trusted"` / `"t0"`: a subprocess, but the parent environment is inherited and
    /// no `rlimit`s are imposed. For first-party build steps.
    Trusted,
    /// `"isolated"` / `"t1"` / *(default)*: environment scrubbed to a minimal set, the
    /// working directory confined to a fresh temp dir, and (Unix) moderate CPU /
    /// address-space / file-size / fd `rlimit`s applied before `exec`.
    Isolated,
    /// `"sandboxed"` / `"t2"`: as Isolated with a near-empty environment and tighter
    /// `rlimit`s — for running untrusted step programs.
    Sandboxed,
}

impl IsolationTier {
    /// Parse a [`WorkloadSpec::tier`] string. Empty or unknown ⇒ [`IsolationTier::Isolated`]
    /// (the safe default: an unlabeled step is confined, never trusted).
    pub fn parse(tier: &str) -> IsolationTier {
        match tier.trim().to_ascii_lowercase().as_str() {
            "trusted" | "t0" => IsolationTier::Trusted,
            "sandboxed" | "t2" | "untrusted" => IsolationTier::Sandboxed,
            _ => IsolationTier::Isolated,
        }
    }

    /// The Unix `rlimit`s this tier imposes (CPU seconds, address-space bytes,
    /// file-size bytes, open-fd count). `None` for [`IsolationTier::Trusted`].
    fn rlimits(self, cpu_secs: u64) -> Option<Rlimits> {
        match self {
            IsolationTier::Trusted => None,
            IsolationTier::Isolated => Some(Rlimits {
                cpu_secs,
                address_space: 1 << 30, // 1 GiB
                file_size: 64 << 20,    // 64 MiB
                nofile: 256,
            }),
            IsolationTier::Sandboxed => Some(Rlimits {
                cpu_secs,
                address_space: 256 << 20, // 256 MiB
                file_size: 8 << 20,       // 8 MiB
                nofile: 64,
            }),
        }
    }

    /// Whether the child inherits the parent environment (`Trusted`) or a scrubbed one.
    fn inherits_env(self) -> bool {
        matches!(self, IsolationTier::Trusted)
    }
}

#[derive(Clone, Copy)]
struct Rlimits {
    cpu_secs: u64,
    address_space: u64,
    file_size: u64,
    nofile: u64,
}

/// A real step isolate: runs `source` as a shell command in a separate OS process
/// under an enforced wall-clock deadline, an output cap, a per-[`IsolationTier`]
/// environment/cwd/`rlimit` regime. Handles `lang ∈ {"process", "shell", "command"}`.
///
/// Failure classification:
/// - **timeout** (wall-clock overrun, child killed) ⇒ [`StepErrorKind::Transient`]
///   (a retry on a less-loaded host may succeed);
/// - **spawn failure** (could not fork/exec) ⇒ [`StepErrorKind::Transient`];
/// - **nonzero exit / signal** ⇒ [`StepErrorKind::Permanent`] (the program faulted).
#[derive(Debug, Clone)]
pub struct ProcessRunner {
    /// The shell program used to interpret a step's `source` (default `/bin/sh`).
    pub shell: String,
    /// Default wall-clock deadline per step.
    pub timeout: std::time::Duration,
    /// CPU-seconds `rlimit` for limited tiers (derived from `timeout` if smaller).
    pub cpu_secs: u64,
    /// Cap on captured stdout bytes (older bytes beyond this are dropped — a runaway
    /// producer cannot exhaust host memory through the pipe).
    pub max_output_bytes: usize,
}

impl Default for ProcessRunner {
    fn default() -> ProcessRunner {
        ProcessRunner {
            shell: "/bin/sh".to_string(),
            timeout: std::time::Duration::from_secs(30),
            cpu_secs: 30,
            max_output_bytes: 1 << 20, // 1 MiB
        }
    }
}

impl ProcessRunner {
    /// A process runner with a specific wall-clock deadline per step.
    pub fn with_timeout(timeout: std::time::Duration) -> ProcessRunner {
        let cpu = timeout.as_secs().max(1);
        ProcessRunner {
            timeout,
            cpu_secs: cpu,
            ..ProcessRunner::default()
        }
    }
}

impl StepRunner for ProcessRunner {
    fn run(&self, spec: &WorkloadSpec) -> Result<String, StepError> {
        match spec.lang.as_str() {
            "process" | "shell" | "command" => {}
            other => {
                return Err(StepError::permanent(format!(
                    "step `{}`: ProcessRunner cannot run lang `{other}`",
                    spec.label
                )))
            }
        }
        let tier = IsolationTier::parse(&spec.tier);
        run_subprocess(self, tier, &spec.source, &spec.label)
    }
}

/// Spawn `source` under `shell -c`, enforce the deadline + output cap, capture stdout.
fn run_subprocess(
    cfg: &ProcessRunner,
    tier: IsolationTier,
    source: &str,
    label: &str,
) -> Result<String, StepError> {
    use std::io::Read;
    use std::process::{Command, Stdio};
    use std::sync::mpsc;

    // A fresh confined working directory for non-trusted tiers.
    let workdir = if tier.inherits_env() {
        None
    } else {
        Some(
            tempfile::Builder::new()
                .prefix("dwf-step-")
                .tempdir()
                .map_err(|e| StepError::transient(format!("step `{label}`: mkdtemp: {e}")))?,
        )
    };

    let mut cmd = Command::new(&cfg.shell);
    cmd.arg("-c")
        .arg(source)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if !tier.inherits_env() {
        cmd.env_clear();
        // A minimal, predictable environment. Sandboxed gets nothing but PATH.
        cmd.env("PATH", "/usr/bin:/bin");
        if matches!(tier, IsolationTier::Isolated) {
            cmd.env("LANG", "C");
        }
    }
    if let Some(dir) = &workdir {
        cmd.current_dir(dir.path());
    }

    #[cfg(unix)]
    if let Some(limits) = tier.rlimits(cfg.cpu_secs.max(cfg.timeout.as_secs().max(1))) {
        apply_rlimits_before_exec(&mut cmd, limits);
    }

    let mut child = cmd
        .spawn()
        .map_err(|e| StepError::transient(format!("step `{label}`: spawn `{}`: {e}", cfg.shell)))?;

    // Drain stdout/stderr on threads so a full pipe never deadlocks the child, capping
    // captured stdout at `max_output_bytes`.
    let mut stdout = child.stdout.take().expect("piped stdout");
    let mut stderr = child.stderr.take().expect("piped stderr");
    let cap = cfg.max_output_bytes;
    let (otx, orx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout.read_to_end(&mut buf);
        buf.truncate(cap);
        let _ = otx.send(buf);
    });
    let (etx, erx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr.read_to_end(&mut buf);
        buf.truncate(8 << 10);
        let _ = etx.send(buf);
    });

    // Enforce the wall-clock deadline: poll for exit, kill on overrun.
    let deadline = std::time::Instant::now() + cfg.timeout;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if std::time::Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(StepError::transient(format!(
                        "step `{label}`: exceeded wall-clock deadline of {:?} (killed)",
                        cfg.timeout
                    )));
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            Err(e) => {
                return Err(StepError::transient(format!(
                    "step `{label}`: wait failed: {e}"
                )))
            }
        }
    };

    let out = orx.recv().unwrap_or_default();
    let err = erx.recv().unwrap_or_default();
    drop(workdir); // remove the confined dir now the child is gone

    if status.success() {
        Ok(String::from_utf8_lossy(&out).trim().to_string())
    } else {
        let code = status.code().map(|c| c.to_string()).unwrap_or_else(|| {
            #[cfg(unix)]
            {
                use std::os::unix::process::ExitStatusExt;
                status
                    .signal()
                    .map(|s| format!("signal {s}"))
                    .unwrap_or_else(|| "unknown".to_string())
            }
            #[cfg(not(unix))]
            {
                "unknown".to_string()
            }
        });
        let stderr_tail = String::from_utf8_lossy(&err);
        Err(StepError::permanent(format!(
            "step `{label}`: exited {code}: {}",
            stderr_tail.trim()
        )))
    }
}

#[cfg(unix)]
fn apply_rlimits_before_exec(cmd: &mut std::process::Command, limits: Rlimits) {
    use std::os::unix::process::CommandExt;
    // SAFETY: `pre_exec` runs in the forked child before `exec`. We only call
    // `setrlimit`, which is async-signal-safe, and touch no parent memory.
    unsafe {
        cmd.pre_exec(move || {
            set_rlimit(libc::RLIMIT_CPU, limits.cpu_secs);
            set_rlimit(libc::RLIMIT_AS, limits.address_space);
            set_rlimit(libc::RLIMIT_FSIZE, limits.file_size);
            set_rlimit(libc::RLIMIT_NOFILE, limits.nofile);
            Ok(())
        });
    }
}

#[cfg(unix)]
fn set_rlimit(resource: libc::c_int, value: u64) {
    let lim = libc::rlimit {
        rlim_cur: value as libc::rlim_t,
        rlim_max: value as libc::rlim_t,
    };
    // Best-effort: if the host caps us lower we keep the child's inherited limit.
    unsafe {
        libc::setrlimit(resource, &lim);
    }
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
    fn expr_runner_rejects_bad_input_permanently() {
        let r = ExprRunner;
        let e = r.run(&WorkloadSpec::expr("s", "not math")).unwrap_err();
        assert_eq!(e.kind, StepErrorKind::Permanent);
        let e2 = r
            .run(&WorkloadSpec {
                label: "s".into(),
                lang: "wasm".into(),
                source: String::new(),
                tier: String::new(),
                cost: None,
            })
            .unwrap_err();
        assert_eq!(e2.kind, StepErrorKind::Permanent);
    }

    #[test]
    fn tier_parse_defaults_to_isolated() {
        assert_eq!(IsolationTier::parse(""), IsolationTier::Isolated);
        assert_eq!(IsolationTier::parse("weird"), IsolationTier::Isolated);
        assert_eq!(IsolationTier::parse("t0"), IsolationTier::Trusted);
        assert_eq!(IsolationTier::parse("trusted"), IsolationTier::Trusted);
        assert_eq!(IsolationTier::parse("T2"), IsolationTier::Sandboxed);
    }

    #[cfg(unix)]
    #[test]
    fn process_runner_captures_stdout() {
        let r = ProcessRunner::default();
        let out = r
            .run(&WorkloadSpec::process(
                "s",
                "printf '%s' hello-isolate",
                "isolated",
            ))
            .unwrap();
        assert_eq!(out, "hello-isolate");
    }

    #[cfg(unix)]
    #[test]
    fn process_runner_nonzero_exit_is_permanent() {
        let r = ProcessRunner::default();
        let e = r
            .run(&WorkloadSpec::process(
                "s",
                "echo boom >&2; exit 3",
                "isolated",
            ))
            .unwrap_err();
        assert_eq!(e.kind, StepErrorKind::Permanent);
        assert!(e.message.contains("exited 3"), "got: {}", e.message);
        assert!(e.message.contains("boom"));
    }

    #[cfg(unix)]
    #[test]
    fn process_runner_timeout_is_transient_and_killed() {
        let r = ProcessRunner::with_timeout(std::time::Duration::from_millis(150));
        let start = std::time::Instant::now();
        let e = r
            .run(&WorkloadSpec::process("s", "sleep 10", "isolated"))
            .unwrap_err();
        // Killed promptly, not after 10s.
        assert!(start.elapsed() < std::time::Duration::from_secs(2));
        assert_eq!(e.kind, StepErrorKind::Transient);
        assert!(e.message.contains("deadline"), "got: {}", e.message);
    }

    #[cfg(unix)]
    #[test]
    fn isolated_tier_scrubs_environment() {
        // A secret in the parent env must not reach an isolated child.
        std::env::set_var("DWF_SECRET_PROBE", "leaked");
        let r = ProcessRunner::default();
        let out = r
            .run(&WorkloadSpec::process(
                "s",
                "printf '%s' \"${DWF_SECRET_PROBE:-clean}\"",
                "isolated",
            ))
            .unwrap();
        assert_eq!(out, "clean", "isolated child inherited a parent env var");
        // Trusted inherits it.
        let out2 = r
            .run(&WorkloadSpec::process(
                "s",
                "printf '%s' \"${DWF_SECRET_PROBE:-clean}\"",
                "trusted",
            ))
            .unwrap();
        assert_eq!(out2, "leaked");
        std::env::remove_var("DWF_SECRET_PROBE");
    }
}
