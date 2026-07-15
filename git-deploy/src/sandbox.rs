//! `sandbox` — the deny-default cage an untrusted-repo build command runs in.
//!
//! A [`BuildPlan::Command`](crate::plan::BuildPlan::Command) executes code the deployed repo
//! controls (`npm run build`, or a manifest `[build].command`). Running that verbatim through
//! `sh -c` with the deploy host's full environment is untrusted-repo RCE (host-secret / cloud-
//! credential exfil, miners, `rm -rf`) with no resource caps (a timeout reaping only the direct
//! `sh`, leaving forked daemons / disk-fillers running). This module is the deny-default floor
//! that closes both:
//!
//! - **`env_clear()` + a minimal allowlist.** The child inherits NONE of the deploy process's
//!   environment — no cloud creds, no settlement/auth keys, no sibling tenant paths. Only a
//!   short list of innocuous build vars (`PATH`, locale) is passed, and `HOME`/`TMPDIR` are
//!   repinned INTO the build workdir (never the deploy user's `$HOME`, which holds the creds
//!   the naive path would leak).
//! - **A fresh process group.** The build leads its own group, so a timeout — and a clean
//!   completion — reap the WHOLE tree (detached grandchildren, double-forked daemons), not just
//!   the `sh` a bare `child.kill()` would catch.
//! - **Resource rlimits** applied in the child between `fork` and `exec`: a file-size cap
//!   (disk-fill), a CPU cap, and — on Linux — an address-space cap (RAM) and a best-effort
//!   empty network namespace + `no_new_privs`. The caps scale with the build [`BuildTier`].
//!
//! This is the locally-enforceable floor (it engages on every deploy host, macOS included). The
//! **hard** isolation boundary is the resident `grain-jail` confined-body cage (firmament
//! process-PD: macOS Seatbelt / Linux seccomp+Landlock) that the same `tier` selects on a fleet
//! node; here the tier is honored as the resource envelope + the deny-default cage — it is never
//! silently discarded.

use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

use crate::plan::BuildTier;

/// Environment variables a build is allowed to inherit from the deploy host. Everything else is
/// wiped by `env_clear()` — in particular every credential/secret-bearing var. `HOME`/`TMPDIR`
/// are deliberately NOT here: they are set fresh, pointed into the workdir.
const ENV_ALLOWLIST: &[&str] = &[
    "PATH", "LANG", "LC_ALL", "LC_CTYPE", "LANGUAGE", "TERM", "TZ",
];

/// A safe default `PATH` when the deploy host did not set one.
const DEFAULT_PATH: &str = "/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin";

/// The build's confined temp dir, created under the workdir (never the deploy user's `$TMPDIR`).
const BUILD_TMP_DIR: &str = ".build-tmp";

/// The resource envelope a sandboxed build runs under. Derived from the [`BuildTier`]
/// ([`SandboxLimits::for_tier`]); a test can pin tighter caps to exercise a PoC quickly.
#[derive(Debug, Clone, Copy)]
pub struct SandboxLimits {
    /// Max size (bytes) of any single file the build may write (`RLIMIT_FSIZE`) — the disk-fill
    /// bound. Enforced on every POSIX host.
    pub fsize_bytes: u64,
    /// Max CPU-seconds the build may consume (`RLIMIT_CPU`) — a runaway-spin backstop.
    pub cpu_secs: u64,
    /// Max address space (bytes) the build may map (`RLIMIT_AS`) — the RAM bound. Enforced on
    /// Linux; macOS does not meaningfully honor `RLIMIT_AS`, so it is a Linux-only tooth.
    pub as_bytes: u64,
}

impl SandboxLimits {
    /// The resource envelope for `tier`, with the CPU cap aligned to the build deadline. Heavier
    /// tiers (MicroVm) get a more generous envelope; the wasm/Caged grades are tight.
    pub fn for_tier(tier: BuildTier, timeout: Duration) -> SandboxLimits {
        let gib = 1024 * 1024 * 1024u64;
        let mib = 1024 * 1024u64;
        // CPU backstop a touch above the wall-clock deadline (wall-clock is the primary bound).
        let cpu_secs = timeout.as_secs().saturating_add(30).max(30);
        match tier {
            BuildTier::Sandboxed | BuildTier::JitSandboxed | BuildTier::Caged => SandboxLimits {
                fsize_bytes: 512 * mib,
                cpu_secs,
                as_bytes: 2 * gib,
            },
            BuildTier::MicroVm => SandboxLimits {
                fsize_bytes: 2 * gib,
                cpu_secs,
                as_bytes: 8 * gib,
            },
        }
    }
}

/// Run `command` via `sh -c` inside the deny-default cage, bounded by `timeout`, at the resource
/// envelope `tier` selects. Returns `Ok(())` on a clean exit; an error on a non-zero exit, a
/// timeout (the whole process group is reaped), or a spawn failure.
pub fn run_sandboxed_command(
    command: &str,
    cwd: &Path,
    tier: BuildTier,
    timeout: Duration,
) -> anyhow::Result<()> {
    run_sandboxed_command_with_limits(
        command,
        cwd,
        timeout,
        SandboxLimits::for_tier(tier, timeout),
    )
}

/// [`run_sandboxed_command`] with an explicit resource envelope (the test seam — a PoC pins a
/// tiny `fsize_bytes` so the disk-fill bound is hit without writing hundreds of MiB).
pub fn run_sandboxed_command_with_limits(
    command: &str,
    cwd: &Path,
    timeout: Duration,
    limits: SandboxLimits,
) -> anyhow::Result<()> {
    let mut cmd = Command::new("sh");
    cmd.arg("-c").arg(command).current_dir(cwd);

    // --- deny-default environment ---
    cmd.env_clear();
    for key in ENV_ALLOWLIST {
        if let Some(val) = std::env::var_os(key) {
            cmd.env(key, val);
        }
    }
    if std::env::var_os("PATH").is_none() {
        cmd.env("PATH", DEFAULT_PATH);
    }
    // HOME + TMPDIR confined to the build workdir — never the deploy user's $HOME (which holds
    // ~/.aws, config keys, …). A build that reads `$HOME/.aws/credentials` now reads inside its
    // own sandbox tree, where there is nothing.
    cmd.env("HOME", cwd);
    let tmp = cwd.join(BUILD_TMP_DIR);
    let _ = std::fs::create_dir_all(&tmp);
    cmd.env("TMPDIR", &tmp);

    #[cfg(unix)]
    harden_unix(&mut cmd, limits);
    #[cfg(not(unix))]
    let _ = limits;

    let mut child = cmd
        .spawn()
        .map_err(|e| anyhow::anyhow!("spawn sandboxed build `{command}`: {e}"))?;
    let pid = child.id();

    let deadline = Instant::now() + timeout;
    let result = loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                if status.success() {
                    break Ok(());
                }
                break Err(anyhow::anyhow!(
                    "build command `{command}` exited with {status}"
                ));
            }
            Ok(None) => {
                if Instant::now() >= deadline {
                    // Reap the whole group, not just `sh` — a double-forked daemon dies too.
                    kill_group(pid);
                    let _ = child.kill();
                    let _ = child.wait();
                    break Err(anyhow::anyhow!(
                        "build command `{command}` exceeded the {}s bound (process group reaped)",
                        timeout.as_secs()
                    ));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => break Err(anyhow::anyhow!("wait on build `{command}`: {e}")),
        }
    };

    // Always sweep the group on the way out: a build that exited cleanly but left a backgrounded
    // grandchild (a miner, a daemon) leaves no survivor.
    kill_group(pid);
    let _ = child.wait();
    result
}

/// SIGKILL the process group led by `pid`. While any group member is alive the kernel reserves
/// `pid` as the pgid, so this targets exactly the build's tree (never a recycled, unrelated pid).
/// A no-op where the group already drained.
#[cfg(unix)]
fn kill_group(pid: u32) {
    // Negative pid ⇒ "the process group whose id is |pid|".
    unsafe {
        libc::kill(-(pid as i32), libc::SIGKILL);
    }
}

#[cfg(not(unix))]
fn kill_group(_pid: u32) {}

/// Apply the POSIX hardening: a fresh process group + resource rlimits (and, on Linux, an
/// address-space cap, an empty network namespace, and `no_new_privs`).
#[cfg(unix)]
fn harden_unix(cmd: &mut Command, limits: SandboxLimits) {
    use std::os::unix::process::CommandExt;

    // The build leads its own process group → a timeout / completion reaps the whole tree.
    cmd.process_group(0);

    // rlimits are set in the child, after fork, before exec — async-signal-safe libc only.
    unsafe {
        cmd.pre_exec(move || {
            set_rlimit(libc::RLIMIT_FSIZE, limits.fsize_bytes);
            set_rlimit(libc::RLIMIT_CPU, limits.cpu_secs);
            #[cfg(target_os = "linux")]
            {
                set_rlimit(libc::RLIMIT_AS, limits.as_bytes);
                // Best-effort, never fatal: drop the build into an empty network namespace (no
                // host network; `curl`/exfil reaches nothing) and forbid privilege escalation.
                // These need unprivileged user namespaces; where the host forbids them the
                // grain-jail fleet cage remains the hard boundary.
                libc::unshare(libc::CLONE_NEWNET);
                libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
            }
            #[cfg(not(target_os = "linux"))]
            let _ = limits.as_bytes;
            Ok(())
        });
    }
}

/// Set both the soft and hard limit of `resource` to `value` (best-effort; a setrlimit failure
/// in the pre-exec child is non-fatal — the build still runs, just less bounded).
#[cfg(unix)]
fn set_rlimit(resource: RlimitResource, value: u64) {
    let rl = libc::rlimit {
        rlim_cur: value as libc::rlim_t,
        rlim_max: value as libc::rlim_t,
    };
    unsafe {
        libc::setrlimit(resource, &rl);
    }
}

// The first arg of `setrlimit` is `__rlimit_resource_t` on glibc-Linux and `c_int` on the
// BSD/macOS libc; alias it so `set_rlimit` is one signature across both.
#[cfg(all(unix, target_os = "linux", target_env = "gnu"))]
type RlimitResource = libc::__rlimit_resource_t;
#[cfg(all(unix, not(all(target_os = "linux", target_env = "gnu"))))]
type RlimitResource = libc::c_int;

#[cfg(test)]
mod tests {
    use super::*;

    fn small_limits() -> SandboxLimits {
        // A 64 KiB file cap so the disk-fill PoC trips fast (no hundreds-of-MiB write).
        SandboxLimits {
            fsize_bytes: 64 * 1024,
            cpu_secs: 30,
            as_bytes: 2 * 1024 * 1024 * 1024,
        }
    }

    /// A malicious build that tries to exfiltrate a host environment variable (the deploy
    /// process holds cloud creds / auth keys / settlement secrets in env) writes NOTHING — no
    /// non-allowlisted parent var reaches the sandboxed child. We pick a variable genuinely
    /// present in the deploy (test) process and NOT on the allowlist, so no process-global env
    /// mutation (and its fork-race) is needed.
    #[test]
    fn parent_env_var_is_not_reachable_from_the_build() {
        let canary = [
            "CARGO_MANIFEST_DIR",
            "CARGO_PKG_NAME",
            "USER",
            "LOGNAME",
            "SHELL",
        ]
        .into_iter()
        .find(|k| std::env::var_os(k).is_some());
        let Some(key) = canary else {
            eprintln!("skipping: no non-allowlisted parent env var present to probe");
            return;
        };
        assert!(
            !ENV_ALLOWLIST.contains(&key),
            "probe var must not be allowlisted"
        );
        let parent_val = std::env::var(key).unwrap();
        assert!(!parent_val.is_empty());

        let dir = tempfile::tempdir().unwrap();
        run_sandboxed_command(
            &format!("printf '%s' \"${{{key}}}\" > leak.txt"),
            dir.path(),
            BuildTier::Caged,
            Duration::from_secs(20),
        )
        .unwrap();
        let leaked = std::fs::read_to_string(dir.path().join("leak.txt")).unwrap_or_default();
        assert!(
            leaked.is_empty(),
            "parent env var `{key}` (={parent_val:?}) leaked into the sandboxed build: {leaked:?}"
        );
    }

    /// The deploy user's `$HOME` is repinned into the workdir, so a build that reads
    /// `$HOME/.aws/credentials` reaches its own (empty) sandbox tree, not the real home.
    #[test]
    fn home_is_repinned_into_the_workdir() {
        let dir = tempfile::tempdir().unwrap();
        run_sandboxed_command(
            "printf '%s' \"$HOME\" > home.txt",
            dir.path(),
            BuildTier::Caged,
            Duration::from_secs(20),
        )
        .unwrap();
        let home = std::fs::read_to_string(dir.path().join("home.txt")).unwrap();
        let want = dir.path().canonicalize().unwrap();
        assert_eq!(
            std::path::Path::new(&home).canonicalize().unwrap(),
            want,
            "HOME must be the build workdir, not the deploy user's home"
        );
    }

    /// A build that writes an unbounded file is bounded by `RLIMIT_FSIZE` — the file is capped,
    /// the host disk is not filled.
    #[cfg(unix)]
    #[test]
    fn disk_fill_is_bounded_by_fsize() {
        let dir = tempfile::tempdir().unwrap();
        // Try to write ~4 MiB; the 64 KiB fsize cap stops it (SIGXFSZ → non-zero exit).
        let _ = run_sandboxed_command_with_limits(
            "dd if=/dev/zero of=big.bin bs=4096 count=1024 2>/dev/null",
            dir.path(),
            Duration::from_secs(20),
            small_limits(),
        );
        let size = std::fs::metadata(dir.path().join("big.bin"))
            .map(|m| m.len())
            .unwrap_or(0);
        assert!(
            size <= 128 * 1024,
            "disk-fill was not bounded: wrote {size} bytes past the 64 KiB cap"
        );
    }

    /// A build that backgrounds a long-lived grandchild and exits cleanly does NOT leave that
    /// process running — the whole group is reaped.
    #[cfg(unix)]
    #[test]
    fn backgrounded_grandchild_is_reaped() {
        let dir = tempfile::tempdir().unwrap();
        run_sandboxed_command(
            "sleep 120 & echo $! > gc.pid",
            dir.path(),
            BuildTier::Caged,
            Duration::from_secs(20),
        )
        .unwrap();
        let pid: i32 = std::fs::read_to_string(dir.path().join("gc.pid"))
            .unwrap()
            .trim()
            .parse()
            .unwrap();
        // Poll briefly for the reap to land; kill(pid, 0) → ESRCH once it's gone.
        let mut alive = true;
        for _ in 0..40 {
            let rc = unsafe { libc::kill(pid, 0) };
            if rc != 0 {
                alive = false;
                break;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        assert!(
            !alive,
            "the backgrounded grandchild (pid {pid}) survived the build"
        );
    }

    /// A legit build still runs: the env allowlist passes `PATH` so tools resolve, and the
    /// command writes its output normally.
    #[test]
    fn legit_build_still_works() {
        let dir = tempfile::tempdir().unwrap();
        run_sandboxed_command(
            "mkdir -p dist && printf '<h1>built</h1>' > dist/index.html",
            dir.path(),
            BuildTier::Caged,
            Duration::from_secs(20),
        )
        .unwrap();
        let body = std::fs::read_to_string(dir.path().join("dist/index.html")).unwrap();
        assert_eq!(body, "<h1>built</h1>");
    }

    /// A non-zero exit is surfaced as an error (not silently swallowed).
    #[test]
    fn failing_build_is_an_error() {
        let dir = tempfile::tempdir().unwrap();
        let err = run_sandboxed_command(
            "exit 3",
            dir.path(),
            BuildTier::Caged,
            Duration::from_secs(20),
        )
        .unwrap_err();
        assert!(err.to_string().contains("exited with"), "got {err}");
    }
}
