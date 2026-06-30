//! `tools` — the **OPERATOR toolkit**: a real, capable agent on a leash.
//!
//! The flat [`Toolkit`](crate::toolkit::Toolkit) wires *named verdict* tools
//! (`run_tests`, `check_health`, the priced `stripe_pay`). [`OperatorTools`] adds
//! the rich, freeform operator surface a real agent needs to *do work*: a real
//! **shell** (workdir-confined cwd, pipes / `&&`, real stdout/stderr/exit), real
//! **fs** (`fs_read` / `fs_write` / `list_dir` / `mkdir`, scoped to a workdir
//! root), real **http** (`http_get`, per-host egress), and **git** (`git_clone`).
//!
//! The dregg point: *every* one of these rides the SAME rail as the flat tools —
//! [`AgentAction::Op`](crate::agent::AgentAction::Op) is **cap-gated** (per-tool
//! AND per-resource: `shell` may be granted yet bounded to `/workdir`; `http` only
//! to `api.github.com`), **metered** (each call drawn from the budget cell), and
//! **receipted** (the result bound into the receipt with a
//! [`WitnessedRun`](crate::agent::WitnessedRun), so a forged "it succeeded" breaks
//! the signature). A capable shell handed *safely*: the cap bundle bounds what it
//! may touch, and the run loop refuses anything outside the grant **before it
//! runs** — no receipt, no effect (the no-amplify teeth).
//!
//! ## The injected-runner seam (no host dependency)
//!
//! Like the compute runner of [`crate::toolkit`], the side-effecting runners are
//! **injected**: the open core owns the cap-gate / meter / receipt / witness
//! binding and the workdir confinement, while the host wires the actual
//! [`ShellFn`] (a `std::process::Command` with a timeout) and [`HttpFn`] (a real
//! HTTP client). `fs` ops are pure-`std` and run in-crate (scoped to the workdir).
//! Tests inject deterministic runners — the cap/meter/receipt braid needs no real
//! shell or network to prove.

use std::collections::BTreeMap;
use std::path::{Component, Path, PathBuf};
use std::sync::Mutex;

use crate::agent::{ToolCall, ToolKit, ToolOutcome, WitnessedRun, op};
use crate::receipt::BodyHasher;
use crate::toolkit::{Toolkit, code_root};

/// What a real shell run produced: the exit code, captured stdout/stderr, and the
/// new working directory (so a `cd` inside the command **persists** to the next
/// shell call — the agent can `cd repo`, then `cargo test`).
#[derive(Clone, Debug, Default)]
pub struct ShellOut {
    /// The process exit status (`0` = success).
    pub exit: i64,
    /// Captured standard output.
    pub stdout: String,
    /// Captured standard error.
    pub stderr: String,
    /// The working directory after the command ran (for `cd` persistence). `None`
    /// leaves the cwd unchanged.
    pub new_cwd: Option<PathBuf>,
}

/// A **shell runner**: run `cmd` with working directory `cwd` and report the real
/// result. The host injects a `std::process::Command` impl with a timeout; tests
/// inject a deterministic stand-in. `Err` is an execution error (couldn't spawn).
pub type ShellFn = Box<dyn Fn(&str, &Path) -> Result<ShellOut, String> + Send + Sync>;

/// What an HTTP GET returned: the status code and the (UTF-8-lossy) body.
#[derive(Clone, Debug, Default)]
pub struct HttpResp {
    /// The HTTP status code.
    pub status: i64,
    /// The response body (UTF-8 lossy; truncated by the tool for the summary).
    pub body: String,
}

/// An **http runner**: GET `url` and report the result. The host injects a real
/// client (reqwest); tests inject a stand-in. `Err` is a transport error.
pub type HttpFn = Box<dyn Fn(&str) -> Result<HttpResp, String> + Send + Sync>;

/// How many bytes of tool output to surface in a verdict summary (the receipt
/// stays compact; the full output is the agent's to act on in-loop).
const SUMMARY_CAP: usize = 600;

/// The **operator toolkit**: the flat/priced [`Toolkit`] (delegated `invoke`) plus
/// the rich operator ops (`shell` / `fs_*` / `http_get` / `git_clone`), all
/// behind the one cap-gated · metered · receipted rail.
pub struct OperatorTools {
    /// The flat + priced tools (`run_tests`, `check_health`, `stripe_pay`).
    inner: Toolkit,
    /// The sandbox root: every fs path is confined under it, the shell starts here.
    workdir: PathBuf,
    /// The persistent shell working directory (starts at `workdir`; a `cd` sticks).
    cwd: Mutex<PathBuf>,
    /// The injected shell runner (also drives `git_clone`).
    shell: Option<ShellFn>,
    /// The injected http runner.
    http: Option<HttpFn>,
}

impl OperatorTools {
    /// An operator toolkit over `inner` (the flat/priced tools) confined to
    /// `workdir`. Wire the side-effecting runners with [`with_shell`] / [`with_http`].
    ///
    /// [`with_shell`]: OperatorTools::with_shell
    /// [`with_http`]: OperatorTools::with_http
    pub fn new(inner: Toolkit, workdir: impl Into<PathBuf>) -> OperatorTools {
        let workdir = workdir.into();
        OperatorTools {
            cwd: Mutex::new(workdir.clone()),
            workdir,
            inner,
            shell: None,
            http: None,
        }
    }

    /// Wire the real shell runner (a `std::process::Command` with a timeout). It
    /// also backs `git_clone`.
    pub fn with_shell(
        mut self,
        f: impl Fn(&str, &Path) -> Result<ShellOut, String> + Send + Sync + 'static,
    ) -> OperatorTools {
        self.shell = Some(Box::new(f));
        self
    }

    /// Wire the real http runner (a reqwest client).
    pub fn with_http(
        mut self,
        f: impl Fn(&str) -> Result<HttpResp, String> + Send + Sync + 'static,
    ) -> OperatorTools {
        self.http = Some(Box::new(f));
        self
    }

    /// The workdir root (the fs/shell sandbox).
    pub fn workdir(&self) -> &Path {
        &self.workdir
    }

    /// Resolve `path` (absolute or relative-to-workdir) to a **lexically
    /// normalized absolute path confined under the workdir**. `Err` if it escapes
    /// the sandbox (a `..` climb out / an absolute path elsewhere) — defense in
    /// depth behind the cap-gate (which already refuses an out-of-prefix resource).
    fn confine(&self, path: &str) -> Result<PathBuf, String> {
        let joined = if Path::new(path).is_absolute() {
            PathBuf::from(path)
        } else {
            self.workdir.join(path)
        };
        let norm = lexical_normalize(&joined);
        if norm.starts_with(&self.workdir) {
            Ok(norm)
        } else {
            Err(format!(
                "path `{path}` escapes the workdir sandbox {}",
                self.workdir.display()
            ))
        }
    }

    /// The confined absolute path string for cap derivation (`""`-resolved on a
    /// sandbox escape, so the cap won't match any in-workdir prefix grant).
    fn confined_str(&self, path: &str) -> String {
        self.confine(path)
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| {
                // An escaping path resolves to its raw absolute form so the cap
                // (e.g. `fs-read:/etc/passwd`) provably falls outside the grant.
                lexical_normalize(Path::new(path))
                    .to_string_lossy()
                    .into_owned()
            })
    }
}

impl ToolKit for OperatorTools {
    fn invoke(
        &self,
        service: &str,
        amount_cents: Option<i64>,
        cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        self.inner.invoke(service, amount_cents, cells)
    }

    fn op_cap(&self, call: &ToolCall) -> String {
        match call.tool.as_str() {
            op::SHELL => "shell".to_string(),
            op::FS_READ | op::LIST_DIR => {
                format!(
                    "fs-read:{}",
                    self.confined_str(call.arg("path").unwrap_or(""))
                )
            }
            op::FS_WRITE | op::MKDIR => {
                format!(
                    "fs-write:{}",
                    self.confined_str(call.arg("path").unwrap_or(""))
                )
            }
            op::HTTP_GET => format!("http:{}", call.url_host("url")),
            op::GIT_CLONE => format!("http:{}", call.url_host("url")),
            other => format!("op:{other}"),
        }
    }

    fn run_op(&self, call: &ToolCall, _cells: &BTreeMap<String, String>) -> ToolOutcome {
        match call.tool.as_str() {
            op::SHELL => self.op_shell(call),
            op::FS_READ => self.op_fs_read(call),
            op::FS_WRITE => self.op_fs_write(call),
            op::LIST_DIR => self.op_list_dir(call),
            op::MKDIR => self.op_mkdir(call),
            op::HTTP_GET => self.op_http_get(call),
            op::GIT_CLONE => self.op_git_clone(call),
            other => ToolOutcome::fail(format!("unknown operator tool `{other}`")),
        }
    }
}

impl OperatorTools {
    fn op_shell(&self, call: &ToolCall) -> ToolOutcome {
        let cmd = call.arg("cmd").unwrap_or("").trim();
        if cmd.is_empty() {
            return ToolOutcome::fail("shell: no `cmd` given");
        }
        let Some(shell) = &self.shell else {
            return ToolOutcome::fail("shell runner not wired on this toolkit");
        };
        let cwd = self.cwd.lock().expect("cwd poisoned").clone();
        match shell(cmd, &cwd) {
            Ok(out) => {
                // Persist a `cd` for the next call (confined back under workdir).
                if let Some(nc) = &out.new_cwd {
                    let nc = lexical_normalize(nc);
                    if nc.starts_with(&self.workdir) {
                        *self.cwd.lock().expect("cwd poisoned") = nc;
                    }
                }
                let body = clip(&join_streams(&out.stdout, &out.stderr));
                let oc = if out.exit == 0 {
                    ToolOutcome::pass(format!("$ {cmd}\n[exit 0]\n{body}"))
                } else {
                    ToolOutcome::fail(format!("$ {cmd}\n[exit {}]\n{body}", out.exit))
                };
                oc.with_witness(witness(
                    &format!("shell[{cmd}]"),
                    &[cmd],
                    out.exit,
                    &[&out.stdout, &out.stderr],
                ))
            }
            Err(e) => ToolOutcome::fail(format!("shell exec error: {e}")),
        }
    }

    fn op_fs_read(&self, call: &ToolCall) -> ToolOutcome {
        let raw = call.arg("path").unwrap_or("");
        let path = match self.confine(raw) {
            Ok(p) => p,
            Err(e) => return ToolOutcome::fail(e),
        };
        match std::fs::read_to_string(&path) {
            Ok(content) => {
                let exit = 0;
                let oc = ToolOutcome::pass(format!(
                    "read {} ({} bytes)\n{}",
                    path.display(),
                    content.len(),
                    clip(&content)
                ));
                oc.with_witness(witness(
                    &format!("fs_read[{}]", path.display()),
                    &[raw],
                    exit,
                    &[&content],
                ))
            }
            Err(e) => ToolOutcome::fail(format!("fs_read {}: {e}", path.display())),
        }
    }

    fn op_fs_write(&self, call: &ToolCall) -> ToolOutcome {
        let raw = call.arg("path").unwrap_or("");
        let content = call.arg("content").unwrap_or("");
        let path = match self.confine(raw) {
            Ok(p) => p,
            Err(e) => return ToolOutcome::fail(e),
        };
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        match std::fs::write(&path, content.as_bytes()) {
            Ok(()) => {
                let oc = ToolOutcome::pass(format!(
                    "wrote {} bytes to {}",
                    content.len(),
                    path.display()
                ));
                oc.with_witness(witness(
                    &format!("fs_write[{}]", path.display()),
                    &[raw, content],
                    0,
                    &[content],
                ))
            }
            Err(e) => ToolOutcome::fail(format!("fs_write {}: {e}", path.display())),
        }
    }

    fn op_list_dir(&self, call: &ToolCall) -> ToolOutcome {
        let raw = call.arg("path").unwrap_or(".");
        let path = match self.confine(raw) {
            Ok(p) => p,
            Err(e) => return ToolOutcome::fail(e),
        };
        match std::fs::read_dir(&path) {
            Ok(rd) => {
                let mut entries: Vec<String> = rd
                    .filter_map(|e| e.ok())
                    .map(|e| {
                        let name = e.file_name().to_string_lossy().into_owned();
                        if e.path().is_dir() {
                            format!("{name}/")
                        } else {
                            name
                        }
                    })
                    .collect();
                entries.sort();
                let listing = entries.join("\n");
                let oc = ToolOutcome::pass(format!(
                    "{} ({} entries)\n{}",
                    path.display(),
                    entries.len(),
                    clip(&listing)
                ));
                oc.with_witness(witness(
                    &format!("list_dir[{}]", path.display()),
                    &[raw],
                    0,
                    &[&listing],
                ))
            }
            Err(e) => ToolOutcome::fail(format!("list_dir {}: {e}", path.display())),
        }
    }

    fn op_mkdir(&self, call: &ToolCall) -> ToolOutcome {
        let raw = call.arg("path").unwrap_or("");
        let path = match self.confine(raw) {
            Ok(p) => p,
            Err(e) => return ToolOutcome::fail(e),
        };
        match std::fs::create_dir_all(&path) {
            Ok(()) => {
                let oc = ToolOutcome::pass(format!("mkdir {}", path.display()));
                oc.with_witness(witness(
                    &format!("mkdir[{}]", path.display()),
                    &[raw],
                    0,
                    &[],
                ))
            }
            Err(e) => ToolOutcome::fail(format!("mkdir {}: {e}", path.display())),
        }
    }

    fn op_http_get(&self, call: &ToolCall) -> ToolOutcome {
        let url = call.arg("url").unwrap_or("").trim();
        if url.is_empty() {
            return ToolOutcome::fail("http_get: no `url` given");
        }
        let Some(http) = &self.http else {
            return ToolOutcome::fail("http runner not wired on this toolkit");
        };
        match http(url) {
            Ok(resp) => {
                let exit = if (200..400).contains(&resp.status) {
                    0
                } else {
                    1
                };
                let summary = format!("GET {url}\n[status {}]\n{}", resp.status, clip(&resp.body));
                let oc = if exit == 0 {
                    ToolOutcome::pass(summary)
                } else {
                    ToolOutcome::fail(summary)
                };
                oc.with_witness(witness(
                    &format!("http_get[{}]", call.url_host("url")),
                    &[url],
                    exit,
                    &[&resp.status.to_string(), &resp.body],
                ))
            }
            Err(e) => ToolOutcome::fail(format!("http_get {url}: {e}")),
        }
    }

    fn op_git_clone(&self, call: &ToolCall) -> ToolOutcome {
        let url = call.arg("url").unwrap_or("").trim();
        if url.is_empty() {
            return ToolOutcome::fail("git_clone: no `url` given");
        }
        let Some(shell) = &self.shell else {
            return ToolOutcome::fail("shell runner (for git) not wired on this toolkit");
        };
        // The clone destination is confined under the workdir (default: the repo
        // name). git is reached through the shell runner — one real egress path.
        let dest = call
            .arg("dest")
            .map(|s| s.to_string())
            .unwrap_or_else(|| repo_name(url));
        let dest_path = match self.confine(&dest) {
            Ok(p) => p,
            Err(e) => return ToolOutcome::fail(e),
        };
        let cmd = format!(
            "git clone --depth 1 {} {}",
            shell_quote(url),
            shell_quote(&dest_path.to_string_lossy())
        );
        let cwd = self.workdir.clone();
        match shell(&cmd, &cwd) {
            Ok(out) => {
                let body = clip(&join_streams(&out.stdout, &out.stderr));
                let oc = if out.exit == 0 {
                    ToolOutcome::pass(format!("cloned {url} → {}\n{body}", dest_path.display()))
                } else {
                    ToolOutcome::fail(format!("git clone {url} [exit {}]\n{body}", out.exit))
                };
                oc.with_witness(witness(
                    &format!("git_clone[{url}]"),
                    &[url, &dest],
                    out.exit,
                    &[&out.stdout, &out.stderr],
                ))
            }
            Err(e) => ToolOutcome::fail(format!("git clone exec error: {e}")),
        }
    }
}

// ── witnessing + small helpers ────────────────────────────────────────────────

/// A [`WitnessedRun`] binding for an op: the command, a `code_root` over the
/// inputs, the exit, and an output digest. Signed into the receipt (so a tampered
/// command / result breaks the signature). Op runs are not in general
/// deterministically re-executable (network, time), so this is a *tamper-evident*
/// binding — not a re-execution claim (that is `run_tests`' job).
fn witness(command: &str, inputs: &[&str], exit: i64, outputs: &[&str]) -> WitnessedRun {
    WitnessedRun {
        command: command.to_string(),
        code_root: code_root(&inputs.join("\u{1f}")),
        exit,
        output_digest: digest(outputs),
    }
}

/// A domain-separated digest over an op's output values.
fn digest(values: &[&str]) -> [u8; 32] {
    let mut h = BodyHasher::new(b"dregg-agent-op-output-digest-v1");
    h.u64(values.len() as u64);
    for v in values {
        h.field(v.as_bytes());
    }
    h.finalize()
}

/// Join stdout and stderr for a summary (stderr labeled when present).
fn join_streams(stdout: &str, stderr: &str) -> String {
    let stderr = stderr.trim_end();
    if stderr.is_empty() {
        stdout.trim_end().to_string()
    } else if stdout.trim_end().is_empty() {
        format!("[stderr] {stderr}")
    } else {
        format!("{}\n[stderr] {stderr}", stdout.trim_end())
    }
}

/// Clip a string to [`SUMMARY_CAP`] bytes (on a char boundary), marking truncation.
fn clip(s: &str) -> String {
    if s.len() <= SUMMARY_CAP {
        return s.to_string();
    }
    let mut end = SUMMARY_CAP;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}… (+{} bytes)", &s[..end], s.len() - end)
}

/// Lexically normalize a path (resolve `.` / `..` without touching the
/// filesystem), so confinement is decidable for paths that don't exist yet.
fn lexical_normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for comp in p.components() {
        match comp {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            other => out.push(other.as_os_str()),
        }
    }
    out
}

/// The repo name from a clone URL (`…/foo.git` → `foo`, `…/foo` → `foo`).
fn repo_name(url: &str) -> String {
    let tail = url
        .trim_end_matches('/')
        .rsplit('/')
        .next()
        .unwrap_or("repo");
    tail.trim_end_matches(".git").to_string()
}

/// Single-quote a string for a `bash -c` command (the git url / dest).
fn shell_quote(s: &str) -> String {
    format!("'{}'", s.replace('\'', "'\\''"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentAction, AgentCloud, AgentSpec, ToolCall, verify_agent_run};
    use crate::grant::CapGrant;

    fn op(tool: &str, kv: &[(&str, &str)]) -> AgentAction {
        AgentAction::Op(ToolCall::new(
            tool,
            kv.iter().map(|(k, v)| (k.to_string(), v.to_string())),
        ))
    }

    /// A deterministic shell stand-in: echoes the command, exit 0.
    fn fake_shell() -> impl Fn(&str, &Path) -> Result<ShellOut, String> + Send + Sync {
        |cmd, cwd| {
            Ok(ShellOut {
                exit: 0,
                stdout: format!("ran `{cmd}` in {}", cwd.display()),
                stderr: String::new(),
                new_cwd: None,
            })
        }
    }

    fn tools(workdir: &Path) -> OperatorTools {
        OperatorTools::new(Toolkit::new(), workdir).with_shell(fake_shell())
    }

    fn tmpdir(tag: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("dregg-tools-{tag}-{}", std::process::id()));
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    // ── a real fs op is cap-gated to the workdir, metered, receipted ──────────
    #[test]
    fn fs_write_and_read_under_workdir_are_metered_and_receipted() {
        let wd = tmpdir("fs");
        let cloud = AgentCloud::from_seed([80u8; 32]);
        let handle = cloud
            .deploy(
                &AgentSpec::new("agent:fs", 10)
                    .with_workdir_fs(wd.to_string_lossy())
                    .with_shell(),
            )
            .unwrap();
        let toolkit = tools(&wd);

        let plan = vec![
            op(
                "fs_write",
                &[("path", "note.txt"), ("content", "hello dregg")],
            ),
            op("fs_read", &[("path", "note.txt")]),
        ];
        let report = cloud.run_with_toolkit(
            &handle,
            &mut crate::agent::PlannedBrain::new(plan),
            &toolkit,
        );
        assert_eq!(report.admitted, 2, "both fs ops admitted under the workdir");
        assert_eq!(report.receipts.len(), 2);
        assert!(report.all_tools_passed(), "{:?}", report.tool_results());
        // The read saw what the write committed (real fs round-trip).
        assert!(
            report.tool_results()[1].2.contains("hello dregg"),
            "{:?}",
            report.tool_results()[1]
        );
        verify_agent_run(&report).expect("the op run re-witnesses");
        std::fs::remove_dir_all(&wd).ok();
    }

    // ── TOOTH: a path OUTSIDE the workdir is refused by the cap-gate ──────────
    #[test]
    fn an_fs_path_outside_the_workdir_is_refused() {
        let wd = tmpdir("escape");
        let cloud = AgentCloud::from_seed([81u8; 32]);
        let handle = cloud
            .deploy(&AgentSpec::new("agent:escape", 10).with_workdir_fs(wd.to_string_lossy()))
            .unwrap();
        let toolkit = tools(&wd);
        // Try to read /etc/passwd (and a ../ climb) — both outside the prefix grant.
        let plan = vec![
            op("fs_read", &[("path", "/etc/passwd")]),
            op("fs_read", &[("path", "../../../../etc/passwd")]),
        ];
        let report = cloud.run_with_toolkit(
            &handle,
            &mut crate::agent::PlannedBrain::new(plan),
            &toolkit,
        );
        assert_eq!(report.admitted, 0, "no out-of-workdir read ran");
        assert_eq!(report.cap_refused, 2, "both are cap-refused");
        assert_eq!(report.receipts.len(), 0, "a refused op leaves no receipt");
        std::fs::remove_dir_all(&wd).ok();
    }

    // ── TOOTH: http to a non-granted host is refused; the granted host runs ───
    #[test]
    fn http_is_gated_per_host() {
        let wd = tmpdir("http");
        let cloud = AgentCloud::from_seed([82u8; 32]);
        let handle = cloud
            .deploy(&AgentSpec::new("agent:http", 10).with_http_host("api.github.com"))
            .unwrap();
        let toolkit = OperatorTools::new(Toolkit::new(), &wd).with_http(|url| {
            Ok(HttpResp {
                status: 200,
                body: format!("body of {url}"),
            })
        });

        let plan = vec![
            op("http_get", &[("url", "https://api.github.com/repos/x/y")]), // granted
            op("http_get", &[("url", "https://evil.example/steal")]),       // NOT granted
        ];
        let report = cloud.run_with_toolkit(
            &handle,
            &mut crate::agent::PlannedBrain::new(plan),
            &toolkit,
        );
        assert_eq!(report.admitted, 1, "only the granted host ran");
        assert_eq!(report.cap_refused, 1, "the other host is refused");
        assert!(report.tool_results()[0].2.contains("api.github.com"));
        verify_agent_run(&report).expect("the http run re-witnesses");
        std::fs::remove_dir_all(&wd).ok();
    }

    // ── TOOTH: a shell op is gated by the `shell` cap (absent ⇒ refused) ──────
    #[test]
    fn shell_requires_the_shell_cap() {
        let wd = tmpdir("shell");
        let cloud = AgentCloud::from_seed([83u8; 32]);
        // This agent has fs but NOT shell.
        let no_shell = cloud
            .deploy(&AgentSpec::new("agent:noshell", 10).with_workdir_fs(wd.to_string_lossy()))
            .unwrap();
        let toolkit = tools(&wd);
        let report = cloud.run_with_toolkit(
            &no_shell,
            &mut crate::agent::PlannedBrain::new(vec![op("shell", &[("cmd", "echo hi")])]),
            &toolkit,
        );
        assert_eq!(report.cap_refused, 1, "shell refused without the cap");
        assert_eq!(report.admitted, 0);

        // With the shell cap, it runs and is receipted.
        let with_shell = cloud
            .deploy(&AgentSpec::new("agent:withshell", 10).with_shell())
            .unwrap();
        let report = cloud.run_with_toolkit(
            &with_shell,
            &mut crate::agent::PlannedBrain::new(vec![op("shell", &[("cmd", "echo hi")])]),
            &toolkit,
        );
        assert_eq!(report.admitted, 1, "shell runs with the cap");
        assert!(report.all_tools_passed());
        verify_agent_run(&report).expect("the shell run re-witnesses");
        std::fs::remove_dir_all(&wd).ok();
    }

    // ── a forged op verdict breaks the receipt signature ──────────────────────
    #[test]
    fn a_forged_op_verdict_breaks_the_receipt() {
        let wd = tmpdir("forge");
        let cloud = AgentCloud::from_seed([84u8; 32]);
        let handle = cloud
            .deploy(&AgentSpec::new("agent:forgeop", 10).with_shell())
            .unwrap();
        // A shell that fails (exit 1).
        let toolkit = OperatorTools::new(Toolkit::new(), &wd).with_shell(|_cmd, _cwd| {
            Ok(ShellOut {
                exit: 1,
                stdout: String::new(),
                stderr: "boom".into(),
                new_cwd: None,
            })
        });
        let mut report = cloud.run_with_toolkit(
            &handle,
            &mut crate::agent::PlannedBrain::new(vec![op("shell", &[("cmd", "false")])]),
            &toolkit,
        );
        assert!(!report.tool_results()[0].1, "honest verdict is fail");
        verify_agent_run(&report).expect("the honest fail re-witnesses");
        // Forge it to "passed" → the signature no longer matches.
        report.receipts[0].tool_ok = Some(true);
        assert!(verify_agent_run(&report).is_err(), "the forge is caught");
        std::fs::remove_dir_all(&wd).ok();
    }

    // ── SCALE: a sub-agent narrows a resource prefix and cannot widen it ──────
    #[test]
    fn a_subagent_narrows_the_workdir_and_cannot_climb_out() {
        let wd = tmpdir("scale");
        let sub = wd.join("sub");
        std::fs::create_dir_all(&sub).unwrap();
        let cloud = AgentCloud::from_seed([85u8; 32]);
        let parent = cloud
            .deploy(&AgentSpec::new("agent:parent", 100).with_workdir_fs(wd.to_string_lossy()))
            .unwrap();
        // The child is confined to the subdirectory only.
        let child = cloud
            .deploy_subagent(
                &parent,
                &AgentSpec::new("agent:parent/child", 50).with_workdir_fs(sub.to_string_lossy()),
            )
            .expect("child narrows the workdir");
        // A widening child (the whole fs) is refused up front.
        let widen = cloud.deploy_subagent(
            &parent,
            &AgentSpec::new("agent:parent/evil", 10)
                .with_grant(CapGrant::Prefix("fs-read:/".into())),
        );
        assert!(matches!(widen, Err(crate::agent::AgentError::Widen { .. })));

        // The child can write inside its narrowed tree…
        let toolkit = tools(&wd);
        let report = cloud.run_with_toolkit(
            &child,
            &mut crate::agent::PlannedBrain::new(vec![op(
                "fs_write",
                &[
                    ("path", sub.join("ok.txt").to_string_lossy().as_ref()),
                    ("content", "x"),
                ],
            )]),
            &toolkit,
        );
        assert_eq!(report.admitted, 1, "child writes inside its subtree");
        // …but NOT in the parent's wider tree (outside the child's narrowed grant).
        let report2 = cloud.run_with_toolkit(
            &child,
            &mut crate::agent::PlannedBrain::new(vec![op(
                "fs_write",
                &[
                    ("path", wd.join("nope.txt").to_string_lossy().as_ref()),
                    ("content", "x"),
                ],
            )]),
            &toolkit,
        );
        assert_eq!(
            report2.cap_refused, 1,
            "child cannot climb to the parent tree"
        );
        std::fs::remove_dir_all(&wd).ok();
    }
}
