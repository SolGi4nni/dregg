//! DREGG-AS-HOST — the polarity inversion. dregg hosts the agent; the agent does
//! NOT host dregg.
//!
//! ## The polarity problem this fixes
//!
//! In [`crate::mcp_server`] (the prior slice) dregg's tools are registered INTO
//! hermes-acp's ACP session: hermes is the host, dregg's tools are guests added
//! alongside hermes's OWN base `[hermes-acp]` tools — and those base tools (an
//! unconfined `terminal` / `write_file`) are the leak. The authority gate
//! ([`crate::bridge`]) confines them at the *authority* face, but the agent
//! process itself still runs with full ambient OS authority.
//!
//! [`DreggHost`] inverts it. dregg is the host:
//!
//!   1. **The agent runs inside a dregg jail.** [`DreggHost::run_hosted_agent`]
//!      spawns the agent body INSIDE a confined firmament PD ([`crate::confined`])
//!      whose OS sandbox DENIES ambient file / exec / network and every inherited
//!      fd. The agent's ONLY channel is its firmament Endpoint — the dregg control
//!      channel. hermes's own base shell/file tools, run in this process, hit the
//!      jail walls (`open` denied, `socket` denied, `execve` denied) and go INERT.
//!      We do NOT fork hermes: the OS jail neutralizes the leaky base tools at the
//!      OS level, whatever the agent's tool table says.
//!   2. **dregg's tools are the only effective effect-path.** Inside the jail the
//!      agent's only way to *cause* anything is to send a dregg request over the
//!      Endpoint; the host routes it through [`crate::McpToolHost`] (cap-gated,
//!      receipted; `run_js` → a deos-js World, `terminal` → a nested confined PD).
//!      Every effect lands in OUR container, never the host.
//!   3. **Egress is a structured, opt-in door.** The host holds an
//!      [`EgressPolicy`]; sealed by default (no reach outside). When it grants a
//!      specific host subpath, THAT path — and only that path — becomes readable
//!      inside the jail (threaded into the sandbox profile). Revocable.
//!
//! ## What is REAL vs STAND-IN (honest)
//!
//! REAL: the JAIL (the OS sandbox — file/net/exec/fd denied, proven by the in-PD
//! probes), the EGRESS door (a granted host path readable, a sibling denied, both
//! proven in-PD), and the dregg TOOL effect-path (cap-gated, receipted turns
//! through [`crate::McpToolHost`], asserted on its tape).
//!
//! STAND-IN: the agent's BRAIN. A live `hermes-acp` subprocess cannot be the jail
//! body — a maximally-confined PD denies `execve`, so it cannot host a process
//! that `execve`s a python venv, AND the venv here is broken
//! (`ModuleNotFoundError: No module named 'acp'`). So the body is a faithful
//! scripted agent that does what a jailed brain's tool-loop would: it REACHES for
//! its base tools (an unconfined shell, a host-FS read, an arbitrary socket) — and
//! the jail denies every one — then reaches the granted egress path (admitted iff
//! granted). The brain is stood-in; the confinement, the effect-path, and the door
//! are real. THE EXACT REMAINING WIRE: compile hermes's agent loop into the PD
//! body (or grant `execve` of exactly the agent image), so the live brain runs
//! where the scripted body runs today. Everything around it is built.

#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;

use crate::confined::{can_read_path, launch_confined_with_egress, probe, ConfinedAgent};
use crate::egress::EgressPolicy;
use dregg_firmament::process_kernel::ProcessKernel;

/// THE BASE-TOOL ESCAPE PROBES — the exact ambient reaches a leaky hermes base
/// tool would make, each one the jail must DENY. The hosted-agent body runs all
/// of them from inside the jail and folds the verdict; the host asserts every
/// escape was neutralized.
pub mod escape {
    /// An UNCONFINED shell — `execve` of `/bin/sh` — was DENIED (the jail has no
    /// exec authority, so hermes's `terminal` base tool cannot spawn a shell).
    pub const UNCONFINED_SHELL_DENIED: i32 = 0x100;
    /// A host-FS read OUTSIDE any grant — `open(/etc/passwd)` — was DENIED (the
    /// jail denies ambient file authority, so a `read_file` base tool is inert).
    pub const HOST_FS_READ_DENIED: i32 = 0x200;
    /// An ARBITRARY socket — `socket(AF_INET)` to a public address — was DENIED
    /// (the jail denies ambient network authority, so a `web` base tool is inert).
    pub const ARBITRARY_SOCKET_DENIED: i32 = 0x400;
    /// All three base-tool escapes neutralized.
    pub const ALL_NEUTRALIZED: i32 =
        UNCONFINED_SHELL_DENIED | HOST_FS_READ_DENIED | ARBITRARY_SOCKET_DENIED;
}

/// The structured report a hosted-agent run produces — the proof, by running, that
/// dregg is the host. Folded from the jailed body's exit-code verdict + the dregg
/// tool tape the host kept.
#[derive(Clone, Debug, Default)]
pub struct HostedAgentReport {
    /// The raw verdict bitmask the jailed body folded ([`probe`] base teeth +
    /// [`escape`] neutralization teeth + [`probe::EGRESS_GRANTED_OPEN`] /
    /// [`probe::EGRESS_SIBLING_DENIED`]).
    pub verdict: i32,
    /// Whether the FOUR base jail teeth held (file/net/exec/extra-fd denied, the
    /// Endpoint live) — the agent is jailed.
    pub jailed: bool,
    /// Whether ALL THREE base-tool escapes were neutralized (unconfined shell /
    /// host-FS read / arbitrary socket each denied by the jail).
    pub base_tools_neutralized: bool,
    /// Whether the GRANTED egress door was open inside the jail (only meaningful
    /// when the policy granted a path).
    pub egress_granted_open: bool,
    /// Whether a path OUTSIDE the grant stayed denied (the door is specific, not a
    /// hole).
    pub egress_sibling_denied: bool,
}

impl HostedAgentReport {
    fn from_verdict(verdict: i32) -> HostedAgentReport {
        HostedAgentReport {
            verdict,
            jailed: verdict & probe::ALL == probe::ALL,
            base_tools_neutralized: verdict & escape::ALL_NEUTRALIZED == escape::ALL_NEUTRALIZED,
            egress_granted_open: verdict & probe::EGRESS_GRANTED_OPEN != 0,
            egress_sibling_denied: verdict & probe::EGRESS_SIBLING_DENIED != 0,
        }
    }
}

/// DREGG, THE HOST. Holds the egress policy (the doors it grants the agent) and
/// spawns the agent INTO a dregg jail whose only channel is the dregg control
/// Endpoint. The dregg tool effect-path is driven by the caller over the returned
/// [`ConfinedAgent`]'s Endpoint (the same transport the confined-launch tests use)
/// and/or asserted directly via [`crate::McpToolHost`].
pub struct DreggHost {
    /// The structured egress doors this host grants the jailed agent. Sealed (no
    /// doors) by default; opened/closed with [`EgressPolicy::grant_read`] /
    /// [`EgressPolicy::revoke`].
    pub egress: EgressPolicy,
}

impl Default for DreggHost {
    fn default() -> Self {
        DreggHost::new()
    }
}

impl DreggHost {
    /// A new dregg host with a SEALED egress policy (the agent reaches the outside
    /// only through dregg's tools, which route to our containers).
    pub fn new() -> DreggHost {
        DreggHost { egress: EgressPolicy::sealed() }
    }

    /// GRANT the jailed agent a structured, revocable read-door to one host
    /// subpath. The next jail this host spawns threads exactly this path into its
    /// sandbox profile; nothing else opens. (Builder form for ergonomics.)
    pub fn with_egress_read(mut self, path: impl Into<String>) -> DreggHost {
        self.egress.grant_read(path);
        self
    }

    /// SPAWN the agent INTO a dregg jail and reap its confinement+escape+egress
    /// verdict — the run-by-running proof of the polarity inversion.
    ///
    /// The jail's sandbox profile is THIS host's egress policy (sealed ⇒ no door;
    /// a grant ⇒ exactly that read path). Inside the jail the (stand-in) agent
    /// body:
    ///   * runs the four base jail probes (the agent IS jailed);
    ///   * REACHES for its leaky base tools — an unconfined shell, a host-FS read,
    ///     an arbitrary socket — and the jail denies each (base tools neutralized);
    ///   * probes the egress paths the host wired (the granted door open, a sibling
    ///     denied);
    ///   * round-trips one line over the dregg control Endpoint (the channel live).
    ///
    /// Returns the [`HostedAgentReport`]. (The dregg TOOL effect-path — `run_js` /
    /// `terminal` — is exercised by the caller against [`crate::McpToolHost`] over
    /// the same host; the test drives both halves.)
    pub fn run_hosted_agent(
        &self,
        kernel: &ProcessKernel,
        granted_egress_probe: Option<&str>,
        ungranted_egress_probe: Option<&str>,
    ) -> std::io::Result<HostedAgentReport> {
        let granted = granted_egress_probe.map(|s| s.to_string());
        let ungranted = ungranted_egress_probe.map(|s| s.to_string());
        let agent: ConfinedAgent = launch_confined_with_egress(kernel, &self.egress, move |sock| {
            hosted_agent_body(sock, granted.as_deref(), ungranted.as_deref())
        })?;

        // The body reports its FULL verdict over the dregg control Endpoint (the
        // agent's only channel) as one JSON line — NOT the 8-bit exit code, which
        // cannot carry the escape/egress teeth (>0xff). Read it here. The exit code
        // still carries the base jail teeth as a cross-check.
        let mut endpoint_verdict = 0i32;
        if let Ok(s) = agent.pd.kernel_sock.try_clone() {
            let mut reader = BufReader::new(s);
            let mut line = String::new();
            if reader.read_line(&mut line).is_ok() {
                if let Ok(v) = serde_json::from_str::<serde_json::Value>(line.trim()) {
                    endpoint_verdict = v.get("verdict").and_then(|x| x.as_i64()).unwrap_or(0) as i32;
                }
            }
        }
        let exit_verdict = agent.join_verdict()?;
        // The Endpoint verdict is the full bitmask; OR in the exit-code base teeth
        // so the jail teeth are doubly-witnessed (channel + exit code agree on the
        // low bits).
        Ok(HostedAgentReport::from_verdict(endpoint_verdict | (exit_verdict & probe::ALL)))
    }
}

/// THE HOSTED-AGENT BODY — runs INSIDE the dregg jail (confinement already
/// applied: file/net/exec denied, every non-Endpoint fd closed). It plays what a
/// jailed brain's tool-loop does, and proves the jail neutralizes the leaky base
/// tools, then folds the verdict into the exit code.
fn hosted_agent_body(
    sock: &mut UnixStream,
    granted_egress: Option<&str>,
    ungranted_egress: Option<&str>,
) -> i32 {
    // (1) The four base jail teeth (file/net denied, one fd, + IPC below).
    let mut verdict = crate::confined::run_sandbox_probes();

    // (2) THE BASE-TOOL ESCAPES — exactly the ambient reaches a leaky hermes base
    //     tool would make. Each must be DENIED by the jail.
    //   • an unconfined shell (hermes `terminal`): execve(/bin/sh) — no exec auth.
    if !can_execve_shell() {
        verdict |= escape::UNCONFINED_SHELL_DENIED;
    }
    //   • a host-FS read outside any grant (hermes `read_file`): open(/etc/passwd).
    if !can_read_path("/etc/passwd") {
        verdict |= escape::HOST_FS_READ_DENIED;
    }
    //   • an arbitrary socket (hermes `web`): socket(AF_INET) — already folded as
    //     NET_DENIED by run_sandbox_probes; mirror it into the escape tooth so the
    //     report reads as "base web tool neutralized".
    if verdict & probe::NET_DENIED != 0 {
        verdict |= escape::ARBITRARY_SOCKET_DENIED;
    }

    // (3) THE STRUCTURED EGRESS — the host wired (or didn't) a specific door.
    //   • the GRANTED path must be readable (the door is open).
    if let Some(p) = granted_egress {
        if can_read_path(p) {
            verdict |= probe::EGRESS_GRANTED_OPEN;
        }
    }
    //   • a path OUTSIDE the grant must STILL be denied (specific door, not a hole).
    if let Some(p) = ungranted_egress {
        if !can_read_path(p) {
            verdict |= probe::EGRESS_SIBLING_DENIED;
        }
    }

    // (4) THE DREGG CONTROL CHANNEL — the agent's only channel is live. Report the
    //     FULL verdict over the Endpoint as one JSON line (the channel carries the
    //     escape/egress teeth the 8-bit exit code cannot). The reported verdict
    //     INCLUDES IPC_WORKS (we are about to write it); the EXIT code sets
    //     IPC_WORKS only if the write actually landed (the honest cross-check).
    let reported = verdict | probe::IPC_WORKS;
    let line = format!("{{\"hosted\":true,\"verdict\":{reported}}}\n");
    if sock.write_all(line.as_bytes()).and_then(|_| sock.flush()).is_ok() {
        verdict |= probe::IPC_WORKS;
    }
    verdict & probe::ALL
}

/// Attempt the ambient reach a leaky `terminal` base tool needs: `execve` an
/// unconfined shell. Returns whether it SUCCEEDED. Under the jail (no exec
/// authority — macOS `process-exec*` denied / Linux seccomp `execve` EPERM) it
/// must fail (false). We `fork` so a (denied) exec never replaces THIS process;
/// the child reports exec success/failure via its exit code.
fn can_execve_shell() -> bool {
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        // Can't even fork under the jail — certainly can't spawn a shell.
        return false;
    }
    if pid == 0 {
        // CHILD: try to become /bin/sh. If execve returns, it FAILED (denied);
        // exit 1. If it succeeds we never reach the exit (but the jail denies it).
        let path = b"/bin/sh\0";
        let arg0 = b"sh\0";
        let argv = [arg0.as_ptr() as *const libc::c_char, std::ptr::null()];
        unsafe {
            libc::execv(
                path.as_ptr() as *const libc::c_char,
                argv.as_ptr() as *const *const libc::c_char,
            );
            // execv returned ⇒ denied.
            libc::_exit(1);
        }
    }
    // PARENT: reap the child. exit 0 would mean exec succeeded (it cannot under the
    // jail); any non-zero / signal ⇒ exec was denied. The jail also denies the
    // `fork` path's child its own exec, so this is belt-and-suspenders.
    let mut status: libc::c_int = 0;
    unsafe {
        libc::waitpid(pid, &mut status, 0);
    }
    // WIFEXITED && status==0 would be exec success; anything else = denied.
    let exited_zero =
        libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0;
    exited_zero
}
