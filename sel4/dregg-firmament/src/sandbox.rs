//! THE OS-SANDBOX CONFINEMENT — Phase-0 of the cross-platform sandboxed
//! firmament (`docs/DREGG-DESKTOP-OS.md §3`, the ambient-authority half of the
//! v1 isolation upgrade).
//!
//! ## What gap this closes
//!
//! [`crate::process_kernel::ProcessKernel::spawn_pd`] forks a child PD with
//! **MMU isolation** (separate page tables) + a `socketpair(AF_UNIX)` control
//! channel + named `shm` regions + the kernel's epoch-tagged cap-handle
//! [`ValidityTable`]. That is the *memory* half of confinement and it is real.
//! But the fork-path child inherits the parent's **ambient authority**: it can
//! still `open()` arbitrary files, `socket(AF_INET)` the network, `execve` a new
//! image, and it keeps every inherited fd. [`ProcessKernel::ISOLATION_FIDELITY`]
//! names exactly this: "MMU enforces address-space separation" but ambient OS
//! authority is NOT yet confined.
//!
//! This module closes that, applied in the child **right after `fork()`, before
//! the PD `body` runs**, via a per-platform [`confine_child`]:
//!
//! - **macOS (enforced + smoke-tested here):** the child closes every fd except
//!   the granted ones (the control socket), then SELF-applies a `(version 1)
//!   (deny default)` Seatbelt/SBPL profile through `sandbox_init(3)`. The profile
//!   allows only: I/O on already-open fds, the minimal `/usr/lib` + dyld /
//!   framework reads a process needs to keep running, plus any explicitly-granted
//!   read paths. It allows NO `network*`, NO `process-exec*`, NO `mach-lookup*`.
//!   The macOS sandbox MUST be self-applied by the child (a parent cannot impose
//!   it) — fine, the child is trusted firmament code between fork and body.
//!
//! - **Linux (compiled here as a cfg-stub, ENFORCED on Linux):**
//!   `unshare(CLONE_NEWUSER|NEWNET|NEWNS|NEWPID)` + a uid-map (an empty net
//!   namespace = no route to any network), `prctl(PR_SET_NO_NEW_PRIVS)`, a
//!   default-deny seccomp-bpf allow-list (`seccompiler`), Landlock path-rules
//!   (`landlock`) for any granted read paths, and `close_range` keeping only the
//!   granted fds. On macOS the Linux body compiles to a no-op stub so the crate
//!   builds on both; it only RUNS on Linux.
//!
//! ## The trust statement (don't-launder-vacuity)
//!
//! What this ENFORCES on macOS: a confined child that tries `open("/etc/passwd")`
//! is denied by the Seatbelt profile; `socket(AF_INET)` fails (no `network*`);
//! the inherited control socket is the only fd it holds; the control round-trip
//! still works. What remains TRUSTED: the confinement is the host OS's
//! (Seatbelt / Linux LSMs), the same trust the MMU isolation already places in
//! the host kernel. The child applies it to ITSELF — it is firmament code we
//! wrote, not the (untrusted) PD payload, and it does so before yielding to the
//! payload `body`, so the payload never runs un-confined.
//!
//! Unix-only, behind the `process-pd-sandbox` feature (which implies
//! `process-pd`).

#![cfg(all(feature = "process-pd-sandbox", unix))]

use std::os::unix::io::RawFd;

/// The OS-authority grant a confined child is given — the cap→OS mapping seed.
///
/// Phase 0 wires the **Endpoint-only** case: the child keeps exactly the
/// `endpoint_fds` it was granted (its control socket) and nothing else; every
/// other fd is closed, and ambient file/network/exec authority is denied. The
/// `read_paths` field is the next slice (a file-cap → an SBPL allowed path on
/// macOS / a Landlock rule on Linux); it is honored where the platform supports
/// it and is empty for the Endpoint-only Phase-0 case.
#[derive(Clone, Debug, Default)]
pub struct Confinement {
    /// The fds the child is allowed to keep open (its granted channels — the
    /// control socket(s)). EVERY other inherited fd is closed. This is the
    /// "the Endpoint is the only channel" guarantee at the fd layer.
    pub endpoint_fds: Vec<RawFd>,
    /// Read-only filesystem paths a file-cap granted the child (the next slice).
    /// macOS: each becomes an SBPL `(allow file-read* (subpath "<p>"))`.
    /// Linux: each becomes a Landlock read rule. Empty for Endpoint-only Phase 0.
    pub read_paths: Vec<String>,
    /// Outbound network endpoints (`"host:port"`) a NET-cap granted the child — the
    /// STRUCTURED EGRESS SOCKET door (e.g. a jailed brain's LLM-provider call).
    /// Deny-default: empty means NO outbound network at all (the Endpoint-only
    /// floor). Each entry opens EXACTLY one host:port and nothing else.
    ///
    /// macOS: each becomes an SBPL `(allow network-outbound (remote ip
    /// "<host>:<port>"))` — a precise, enforced allow (host must be a literal IP or
    /// `localhost`; a hostname is emitted verbatim and only matches if the OS
    /// resolves it, so a real hostname provider needs a pre-resolved IP or the
    /// in-jail-DNS caveat, see `deos-hermes`). Linux: HONORED via a seccomp
    /// `connect`-NOTIFICATION door (see [`super::provider_door`] + the `linux`
    /// backend). The jailed body may `socket()`, but every `connect()` traps to a
    /// trusted supervisor (firmament code kept in the connected net namespace) that
    /// admits EXACTLY the granted endpoints — establishing the connection on the
    /// child's behalf and injecting the connected fd — and `EPERM`s every other
    /// target. The child's own net namespace stays EMPTY, so deny-default is
    /// structural (no route exists; the ONLY reachable endpoint is one the
    /// supervisor opens after a pure `admits` match). Empty `net_out` ⇒ the fully
    /// net-sealed jail (socket denied), byte-identical to before. (The connect-
    /// notify RUNTIME is validated on a Linux host / CI; the policy+cBPF config
    /// layer is unit-tested and the backend cross-builds for Linux.)
    pub net_out: Vec<String>,

    // ─────────────────── the HEAVY-BODY tier (additive) ───────────────────────
    //
    // The Endpoint-only + read/egress fields above are the LIGHT jail (a compute
    // PD over the control socket). The fields below open the doors a HEAVY body —
    // the confined homeserver grain (`docs/deos/GRAIN-HOMESERVER.md`) — needs to
    // BOOT + SERVE under the SAME deny-default profile: a writable db subpath, a
    // loopback listen, a NAMED mach allow-list, the system read/machinery bundle,
    // and the one execve door for the grain image. Every one is emitted ONLY when
    // its field is set, so a `Confinement::default()` (all empty) still emits the
    // EXACT light-jail profile — the heavy tier is strictly additive. The precise
    // allow-set mirrors the de-risked reference profile
    // `deos-homeserver/sandbox/homeserver.sb` (which boots continuwuity + serves
    // `GET /_matrix/client/versions → 200` under macOS Seatbelt).
    /// Writable filesystem subpaths a WRITE-cap granted the child — the db-dir
    /// door. macOS: each becomes BOTH `(allow file-read* (subpath "<p>"))` AND
    /// `(allow file-write* (subpath "<p>"))` (RocksDB reads back what it writes),
    /// mirroring `homeserver.sb`'s `DB_DIR` grant. Callers pass a CANONICAL
    /// `/private/var/…` path (`with_write_path` canonicalizes best-effort — on
    /// macOS `/tmp`,`/var` are symlinks into `/private`, and the sandbox kernel
    /// checks writes against the resolved path). Empty ⇒ NO writable path.
    pub write_paths: Vec<String>,

    /// Loopback listen addresses (`"127.0.0.1:PORT"`, or `"127.0.0.1:*"` for an
    /// ephemeral self-selected port) a LISTEN-cap granted the child. macOS: each
    /// becomes `(allow network-bind (local ip "localhost:PORT"))` +
    /// `(allow network-inbound (local ip "localhost:PORT"))` — loopback ONLY (a
    /// non-loopback host is dropped). Empty ⇒ NO inbound. This is the firmament
    /// listen door; `homeserver.sb` uses `localhost:*` because the step-1 bin
    /// self-selects an ephemeral port (the tighter per-port door pins ONE port).
    pub listen_addrs: Vec<String>,

    /// The NAMED mach-service allow-list — the CoreFoundation/Security/etc.
    /// global-names a loopback tokio+rocksdb+rustls process resolves. macOS: each
    /// becomes `(allow mach-lookup (global-name "<name>"))` — a NAMED allow-list,
    /// NEVER a blanket `(allow mach-lookup)`. Empty ⇒ NO mach-lookup (a bare Rust
    /// closure body needs none). `with_homeserver_mach_defaults` loads the
    /// de-risked 10.
    pub mach_services: Vec<String>,

    /// Whether to emit the system READ bundle + process/thread MACHINERY the
    /// de-risk profile lists (dyld firmlink `/`, `/usr/lib`, `/System`, the
    /// `/dev/*` char devices, `/etc`+`/private/etc`, timezone db, `$HOMEBREW`,
    /// plus `process-fork`/`sysctl-read`/`system-socket`/signal-self/process-info).
    /// A heavy body (rocksdb bg threads + tokio worker pool) needs it to KEEP
    /// RUNNING; the light jail does not. `false` ⇒ none of it emitted (the light
    /// jail is unchanged). Set by [`Confinement::with_system_reads`].
    pub system_reads: bool,

    /// The `$HOMEBREW` prefix whose subpath the system-read bundle grants (rocksdb
    /// + its compression dylibs live there). Only consulted when `system_reads`.
    /// `None` ⇒ `with_system_reads` fills a detected default (`$HOMEBREW_PREFIX`
    /// or `/opt/homebrew`).
    pub homebrew_prefix: Option<String>,

    /// The ONE binary the child is granted `execve` of — the grain-image door.
    /// macOS: emits BOTH `(allow process-exec (literal "<path>"))` AND
    /// `(allow file-read* (literal "<path>"))` (the image must be readable to be
    /// exec'd), mirroring `homeserver.sb`'s `SELF`. `None` ⇒ NO exec (the light
    /// jail denies all `process-exec`). Set by [`Confinement::with_exec_image`];
    /// consumed by [`super::process_kernel::ProcessKernel::spawn_pd_confined_exec`].
    pub exec_image: Option<String>,
}

impl Confinement {
    /// The Endpoint-only confinement (Phase 0): keep just the control socket fd,
    /// deny all ambient file / network / exec authority, grant no extra paths.
    pub fn endpoint_only(control_fd: RawFd) -> Self {
        Confinement {
            endpoint_fds: vec![control_fd],
            ..Default::default()
        }
    }

    /// Add the granted control/channel fds.
    pub fn with_fds(mut self, fds: impl IntoIterator<Item = RawFd>) -> Self {
        self.endpoint_fds.extend(fds);
        self
    }

    /// Grant a read-only path (a file-cap → an OS path rule). The next slice
    /// past Endpoint-only.
    pub fn with_read_path(mut self, path: impl Into<String>) -> Self {
        self.read_paths.push(path.into());
        self
    }

    /// Grant ONE outbound network endpoint (`"host:port"`) — the structured egress
    /// SOCKET door (a net-cap → an OS network-allow rule). Deny-default: without a
    /// grant the child has no outbound network at all; with it, EXACTLY this
    /// host:port opens and every other remote stays denied.
    pub fn with_net_out(mut self, endpoint: impl Into<String>) -> Self {
        self.net_out.push(endpoint.into());
        self
    }

    // ─────────────────── the HEAVY-BODY tier builders ─────────────────────────

    /// Grant a WRITABLE subpath (a write-cap → the db-dir door). Canonicalizes
    /// best-effort (on macOS `/tmp`,`/var` are symlinks into `/private`; RocksDB
    /// opens the resolved path, so the sandbox rule must be the canonical one). If
    /// the path does not yet exist, the input is used verbatim (the caller passed
    /// an already-canonical `/private/var/…`). Emits BOTH a read AND a write allow.
    pub fn with_write_path(mut self, path: impl AsRef<std::path::Path>) -> Self {
        let p = std::fs::canonicalize(path.as_ref())
            .map(|c| c.to_string_lossy().into_owned())
            .unwrap_or_else(|_| path.as_ref().to_string_lossy().into_owned());
        self.write_paths.push(p);
        self
    }

    /// Grant a LOOPBACK listen (a listen-cap → the firmament listen door). `addr`
    /// is `"127.0.0.1:PORT"` for a pinned port, or `"127.0.0.1:*"` for the
    /// ephemeral self-selected port a step-1 bin picks. Loopback ONLY — a
    /// non-loopback host opens no inbound. Emits the `network-bind` +
    /// `network-inbound` pair on `localhost:PORT`.
    pub fn with_listen(mut self, addr: impl Into<String>) -> Self {
        self.listen_addrs.push(addr.into());
        self
    }

    /// Grant ONE mach service by global-name (an entry in the NAMED allow-list,
    /// never a blanket). Emits `(allow mach-lookup (global-name "<name>"))`.
    pub fn with_mach_service(mut self, name: impl Into<String>) -> Self {
        self.mach_services.push(name.into());
        self
    }

    /// Load the de-risked 10 mach services a loopback tokio+rocksdb+rustls
    /// homeserver resolves (`deos-homeserver/sandbox/homeserver.sb`). A NAMED
    /// allow-list — every entry is one it actually looks up; nothing else opens.
    pub fn with_homeserver_mach_defaults(mut self) -> Self {
        for name in HOMESERVER_MACH_SERVICES {
            self.mach_services.push((*name).to_string());
        }
        self
    }

    /// Emit the system READ bundle + process/thread MACHINERY a heavy body needs
    /// to keep running (see the [`Confinement::system_reads`] field). Fills
    /// `homebrew_prefix` with a detected default (`$HOMEBREW_PREFIX` or
    /// `/opt/homebrew`) if not already set via [`Self::with_homebrew_prefix`].
    pub fn with_system_reads(mut self) -> Self {
        self.system_reads = true;
        if self.homebrew_prefix.is_none() {
            let hb =
                std::env::var("HOMEBREW_PREFIX").unwrap_or_else(|_| "/opt/homebrew".to_string());
            self.homebrew_prefix = Some(hb);
        }
        self
    }

    /// Set the `$HOMEBREW` prefix the system-read bundle grants (rocksdb + its
    /// compression dylibs). Call before/after [`Self::with_system_reads`].
    pub fn with_homebrew_prefix(mut self, prefix: impl Into<String>) -> Self {
        self.homebrew_prefix = Some(prefix.into());
        self
    }

    /// Grant `execve` of EXACTLY this one binary — the grain-image door. Emits the
    /// `process-exec` literal AND a `file-read*` literal (the image must be
    /// readable to be exec'd). Consumed by
    /// [`super::process_kernel::ProcessKernel::spawn_pd_confined_exec`].
    pub fn with_exec_image(mut self, path: impl Into<String>) -> Self {
        self.exec_image = Some(path.into());
        self
    }
}

/// The de-risked 10 mach global-names a loopback continuwuity homeserver resolves
/// (from `deos-homeserver/sandbox/homeserver.sb`) — a NAMED allow-list.
pub const HOMESERVER_MACH_SERVICES: &[&str] = &[
    "com.apple.system.notification_center",
    "com.apple.system.logger",
    "com.apple.system.opendirectoryd.libinfo",
    "com.apple.system.opendirectoryd.membership",
    "com.apple.trustd",
    "com.apple.trustd.agent",
    "com.apple.SecurityServer",
    "com.apple.SystemConfiguration.configd",
    "com.apple.CoreServices.coreservicesd",
    "com.apple.diagnosticd",
];

/// The outcome of a [`confine_child`] attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfineError {
    /// `sandbox_init` (macOS) failed with this message.
    SandboxInit(String),
    /// A Linux confinement step (unshare / prctl / seccomp / landlock) failed.
    Linux(String),
    /// Closing the non-granted fds failed.
    FdClose(String),
    /// This platform has no implemented backing (neither macOS nor Linux).
    Unsupported,
}

impl std::fmt::Display for ConfineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfineError::SandboxInit(m) => write!(f, "macOS sandbox_init failed: {m}"),
            ConfineError::Linux(m) => write!(f, "linux confinement failed: {m}"),
            ConfineError::FdClose(m) => write!(f, "closing inherited fds failed: {m}"),
            ConfineError::Unsupported => write!(f, "no sandbox backing on this platform"),
        }
    }
}

impl std::error::Error for ConfineError {}

/// CONFINE the calling process (a freshly-forked child PD) to its granted
/// authority — close all non-granted fds, then drop ambient OS authority via the
/// host sandbox. Call this in the CHILD, after `fork()`, BEFORE the PD `body`.
///
/// After it returns `Ok(())`, the child can talk over its granted fd(s) but
/// cannot open arbitrary files, reach the network, exec a new image, or touch
/// any other inherited fd. On macOS this is the Seatbelt profile; on Linux the
/// namespaces + seccomp + Landlock stack.
///
/// # Safety
/// MUST be called in a forked child (it mutates process-global authority and
/// closes fds). It is async-signal-safe-ish: it does a bounded amount of work
/// and applies an irreversible confinement; never call it in the parent.
pub fn confine_child(c: &Confinement) -> Result<(), ConfineError> {
    close_all_but(&c.endpoint_fds)?;
    #[cfg(target_os = "macos")]
    {
        macos::confine(c)
    }
    #[cfg(target_os = "linux")]
    {
        linux::confine(c)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = c;
        Err(ConfineError::Unsupported)
    }
}

/// Close EVERY open fd except the granted ones (and the std streams 0/1/2, kept
/// so the PD can still print under `--nocapture` — they are not an authority
/// channel, just the console). This is the fd-isolation half: after it, the
/// granted control socket is the only NON-console channel the child holds.
///
/// We walk a generous fd range and `close` each not in `keep`. (The
/// `close_range(2)` syscall is the spawn-path optimization; the fork path here
/// walks explicitly so it works identically on macOS + Linux without the newer
/// syscall.)
fn close_all_but(keep: &[RawFd]) -> Result<(), ConfineError> {
    // Keep std streams so PD prints survive; keep the granted channel fds.
    let max = max_open_fds();
    for fd in 3..max {
        if keep.contains(&fd) {
            continue;
        }
        // Best-effort: ignore EBADF (already-closed) — only a real failure on a
        // KEPT fd would matter, and we never close those.
        unsafe {
            libc::close(fd);
        }
    }
    Ok(())
}

/// An upper bound on the fd table to sweep. Uses `RLIMIT_NOFILE` soft limit,
/// clamped to a sane ceiling so we never spin over a 2^31 limit.
fn max_open_fds() -> RawFd {
    let mut rl = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    let cap: RawFd = 4096;
    let rc = unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut rl) };
    if rc == 0 && rl.rlim_cur != libc::RLIM_INFINITY {
        (rl.rlim_cur as RawFd).min(cap).max(16)
    } else {
        cap
    }
}

// ───────────────── the provider-egress door — PURE policy layer ──────────────
//
// The Linux provider-only egress door is a seccomp USER-NOTIFICATION filter on
// `connect(2)`: the jailed body may `socket()`, but every `connect()` traps to a
// trusted supervisor (firmament code, outside the jail, in a still-connected net
// namespace) that checks the target `host:port` against the granted `net_out` and
// either establishes the connection ON THE CHILD'S BEHALF (injecting the connected
// fd back) or returns `EPERM`. This is the SOUNDEST of the tractable mechanisms:
//   * deny-default is STRUCTURAL — the child never holds a network route at all
//     (its net namespace stays empty); the ONLY way a byte leaves is a
//     supervisor-mediated, endpoint-checked, pre-established connection. A bug in
//     the plumbing fails CLOSED (a dead supervisor ⇒ `connect` → `ENOSYS`).
//   * it needs NO external binary (unlike slirp4netns) and NO host-network
//     mutation (unlike a veth+nftables NAT), and it precisely matches the existing
//     provider-door test, which points the jail at a HOST loopback listener
//     (`127.0.0.1:port`): the supervisor runs in the host netns, so a granted
//     loopback connect "just works", exactly as macOS Seatbelt filters a shared
//     stack.
//
// This module is the PURE, platform-neutral policy layer (compiled everywhere, so
// it is unit-testable on a macOS dev host): it decides the door MODE from
// `net_out`, parses grants into match targets, builds the connect-filter cBPF
// program, and answers the one fail-OPEN-critical question — "is THIS connect
// target a granted endpoint?". Every other failure in the Linux runtime below
// fails closed, so this admission decision is the load-bearing security kernel and
// is exercised hard by the unit tests.
//
// (On a non-Linux dev host the runtime backend that consumes this is `cfg`-ed
// out, so the builder/consts are used only by the unit tests — allow the dead
// code there rather than scatter per-item attributes.)
#[cfg_attr(not(target_os = "linux"), allow(dead_code))]
pub(crate) mod provider_door {
    /// Which egress door the jail installs, decided purely from `net_out`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum DoorMode {
        /// No grant ⇒ the jail is fully net-sealed (empty net namespace + a seccomp
        /// allow-list that OMITS `socket`). Deny-default, byte-identical to the
        /// pre-door jail.
        Sealed,
        /// One or more granted endpoints ⇒ the connect-notify door (allow `socket`,
        /// trap `connect` to the supervisor). Every ungranted target stays denied.
        ProviderNotify,
    }

    /// Pick the door mode from the granted outbound endpoints. Empty ⇒ `Sealed`
    /// (the deny-default floor); any grant ⇒ the supervised connect-notify door.
    pub fn door_mode(net_out: &[String]) -> DoorMode {
        if net_out.is_empty() {
            DoorMode::Sealed
        } else {
            DoorMode::ProviderNotify
        }
    }

    /// A parsed grant target. A literal-IPv4 (or the `localhost` token) grant is a
    /// concrete `V4` match; a hostname grant is a `Host` the SUPERVISOR resolves
    /// (it has real network) to the IPs it admits — the in-jail-DNS caveat, mirrored
    /// from the macOS SBPL `remote ip` note.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum AllowedEndpoint {
        /// A concrete IPv4 + port the connect target must equal.
        V4([u8; 4], u16),
        /// A hostname + port the supervisor resolves to admitted IPv4s.
        Host(String, u16),
    }

    /// Parse ONE `"host:port"` grant into a match target. `localhost` and dotted
    /// IPv4 become `V4`; anything else is a `Host` for supervisor-side resolution.
    /// `None` if the port is missing/invalid.
    pub fn parse_grant(s: &str) -> Option<AllowedEndpoint> {
        let (host, port_s) = s.rsplit_once(':')?;
        if host.is_empty() {
            return None;
        }
        let port: u16 = port_s.parse().ok()?;
        if host == "localhost" {
            return Some(AllowedEndpoint::V4([127, 0, 0, 1], port));
        }
        if let Some(v4) = parse_ipv4(host) {
            return Some(AllowedEndpoint::V4(v4, port));
        }
        Some(AllowedEndpoint::Host(host.to_string(), port))
    }

    /// Parse the whole `net_out` grant list into match targets (skipping malformed
    /// entries — a malformed grant simply opens no door, never a wildcard).
    pub fn expand_static_grants(net_out: &[String]) -> Vec<AllowedEndpoint> {
        net_out.iter().filter_map(|s| parse_grant(s)).collect()
    }

    /// Parse a dotted-quad IPv4 literal.
    fn parse_ipv4(h: &str) -> Option<[u8; 4]> {
        let mut o = [0u8; 4];
        let mut n = 0;
        for (i, part) in h.split('.').enumerate() {
            if i >= 4 {
                return None;
            }
            o[i] = part.parse().ok()?;
            n += 1;
        }
        if n == 4 {
            Some(o)
        } else {
            None
        }
    }

    /// THE FAIL-OPEN-CRITICAL DECISION — is the connect target `(ip, port)` a
    /// granted endpoint? `allowed_v4` is the concrete match set the supervisor
    /// computed (literal grants verbatim + each `Host` grant's resolved IPv4s). A
    /// target is admitted iff it EXACTLY equals a granted `(ip, port)`; a different
    /// port or a different host is denied. This is the only path to an open door, so
    /// it is deliberately a total, allocation-free, exact-match check.
    pub fn admits(allowed_v4: &[([u8; 4], u16)], ip: [u8; 4], port: u16) -> bool {
        allowed_v4.iter().any(|&(a, p)| a == ip && p == port)
    }

    // ── the connect-notify cBPF program (pure builder, unit-tested for shape) ──

    /// The Linux `AUDIT_ARCH_*` tokens a seccomp filter pins in its arch guard (not
    /// in `libc` for these arches, so named here). A syscall arriving under any
    /// other arch token is killed (defence against a 32-bit-ABI bypass).
    #[allow(dead_code)] // one token is live per target arch; the other is inert.
    pub const AUDIT_ARCH_X86_64: u32 = 0xC000_003E;
    #[allow(dead_code)]
    pub const AUDIT_ARCH_AARCH64: u32 = 0xC000_00B7;

    /// One classic-BPF instruction (layout-identical to `libc::sock_filter`, but
    /// defined here so the builder + its tests compile on non-Linux dev hosts).
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct BpfInsn {
        pub code: u16,
        pub jt: u8,
        pub jf: u8,
        pub k: u32,
    }

    // BPF opcodes / seccomp return values used by the filter.
    const BPF_LD_W_ABS: u16 = 0x20; // BPF_LD | BPF_W | BPF_ABS
    const BPF_JMP_JEQ_K: u16 = 0x15; // BPF_JMP | BPF_JEQ | BPF_K
    const BPF_RET_K: u16 = 0x06; // BPF_RET | BPF_K
    const OFF_NR: u32 = 0; // seccomp_data.nr
    const OFF_ARCH: u32 = 4; // seccomp_data.arch
    const RET_ERRNO_EPERM: u32 = 0x0005_0000 | 1; // SECCOMP_RET_ERRNO | EPERM
    const RET_ALLOW: u32 = 0x7fff_0000; // SECCOMP_RET_ALLOW
    const RET_USER_NOTIF: u32 = 0x7fc0_0000; // SECCOMP_RET_USER_NOTIF
    const RET_KILL_PROCESS: u32 = 0x8000_0000; // SECCOMP_RET_KILL_PROCESS

    /// Build the connect-notify seccomp cBPF program: guard the arch, then for each
    /// `allow_nr` return `ALLOW`, for `notify_nr` (`connect`) return `USER_NOTIF`
    /// (trap to the supervisor), and for everything else return `EPERM`. A syscall
    /// under a foreign arch token is killed. This mirrors the sealed allow-list but
    /// (a) ADDS `socket` (so the child can create the socket the supervisor will
    /// connect) and (b) routes `connect` to the notification listener instead of
    /// denying it.
    pub fn build_connect_seccomp_bpf(arch: u32, allow_nrs: &[i64], notify_nr: i64) -> Vec<BpfInsn> {
        // Layout: [0]=load arch, [1]=arch guard, [2]=load nr,
        //         [3 .. 3+cmp)=comparisons, then DENY, ALLOW, NOTIFY, KILL.
        let cmp = allow_nrs.len() + 1; // one JEQ per allow + one for connect.
        let deny_i = 3 + cmp;
        let allow_i = deny_i + 1;
        let notify_i = allow_i + 1;
        let kill_i = notify_i + 1;

        let mut v = Vec::with_capacity(kill_i + 1);
        // [0] A = seccomp_data.arch
        v.push(BpfInsn {
            code: BPF_LD_W_ABS,
            jt: 0,
            jf: 0,
            k: OFF_ARCH,
        });
        // [1] if A == arch fall through (jt=0); else jump to KILL.
        v.push(BpfInsn {
            code: BPF_JMP_JEQ_K,
            jt: 0,
            jf: (kill_i - 2) as u8, // from index 1 to kill_i: kill_i - 1 - 1
            k: arch,
        });
        // [2] A = seccomp_data.nr
        v.push(BpfInsn {
            code: BPF_LD_W_ABS,
            jt: 0,
            jf: 0,
            k: OFF_NR,
        });
        // comparisons — each allow-nr jumps forward to ALLOW; connect to NOTIFY.
        for (p, &nr) in allow_nrs.iter().enumerate() {
            let abs = 3 + p;
            v.push(BpfInsn {
                code: BPF_JMP_JEQ_K,
                jt: (allow_i - abs - 1) as u8,
                jf: 0,
                k: nr as u32,
            });
        }
        {
            let abs = 3 + allow_nrs.len();
            v.push(BpfInsn {
                code: BPF_JMP_JEQ_K,
                jt: (notify_i - abs - 1) as u8,
                jf: 0,
                k: notify_nr as u32,
            });
        }
        // DENY (fall-through) / ALLOW / NOTIFY / KILL.
        v.push(BpfInsn {
            code: BPF_RET_K,
            jt: 0,
            jf: 0,
            k: RET_ERRNO_EPERM,
        });
        v.push(BpfInsn {
            code: BPF_RET_K,
            jt: 0,
            jf: 0,
            k: RET_ALLOW,
        });
        v.push(BpfInsn {
            code: BPF_RET_K,
            jt: 0,
            jf: 0,
            k: RET_USER_NOTIF,
        });
        v.push(BpfInsn {
            code: BPF_RET_K,
            jt: 0,
            jf: 0,
            k: RET_KILL_PROCESS,
        });
        v
    }
}

// ───────────────────────────── macOS backend ────────────────────────────────

#[cfg(target_os = "macos")]
mod macos {
    use super::{ConfineError, Confinement};
    use std::ffi::{CStr, CString};
    use std::os::raw::{c_char, c_int};
    use std::ptr;

    // The Seatbelt FFI (the `gaol`-macos backend shape, ~10 lines of raw FFI).
    // `sandbox_init` self-applies an SBPL profile to the calling process; once
    // applied it cannot be loosened. `sandbox_free_error` frees the error buffer.
    extern "C" {
        fn sandbox_init(profile: *const c_char, flags: u64, errorbuf: *mut *mut c_char) -> c_int;
        fn sandbox_free_error(errorbuf: *mut c_char);
    }

    /// The default-deny SBPL prologue. Everything not explicitly allowed below
    /// is DENIED — no network, no exec, no mach-lookup, no arbitrary file read.
    const PROLOGUE: &str = "(version 1)\n(deny default)\n";

    /// The minimal allow-set a confined firmament PD needs to KEEP RUNNING after
    /// `sandbox_init` (the dynamic linker / libsystem are already mapped, but the
    /// process may still touch them; a stricter profile risks SIGKILL on the
    /// next libc call). We allow:
    ///   - I/O on already-open fds (the control socket round-trip + console);
    ///   - read-only access to the system dylib/framework paths the runtime maps;
    ///   - sysctl reads libsystem performs.
    /// We do NOT allow network*, process-exec*, process-fork*, mach-lookup*, or
    /// arbitrary file-write — those are the ambient authority we are dropping.
    const BASE_ALLOW: &str = "\
(allow file-read* (subpath \"/usr/lib\"))\n\
(allow file-read* (subpath \"/System/Library\"))\n\
(allow file-read* (subpath \"/Library/Apple\"))\n\
(allow file-read-metadata)\n\
(allow sysctl-read)\n\
(allow file-ioctl)\n\
(allow signal (target self))\n\
";

    /// Build the full SBPL profile text from the prologue, the base allow-set,
    /// and any explicitly-granted read paths (the file-cap → allowed-path map).
    pub(super) fn build_profile(c: &Confinement) -> String {
        let mut p = String::with_capacity(256);
        p.push_str(PROLOGUE);
        p.push_str(BASE_ALLOW);
        for path in &c.read_paths {
            // (allow file-read* (subpath "<path>")) — a granted read path.
            p.push_str("(allow file-read* (subpath \"");
            // Escape backslash + quote for the TinyScheme string literal.
            for ch in path.chars() {
                if ch == '"' || ch == '\\' {
                    p.push('\\');
                }
                p.push(ch);
            }
            p.push_str("\"))\n");
        }
        for endpoint in &c.net_out {
            // (allow network-outbound (remote ip "<host>:<port>")) — ONE granted
            // outbound endpoint (the structured egress socket door). Nothing else
            // network* is allowed, so every other remote stays denied by the
            // (deny default). The `socket(2)` creation itself is not a `network*`
            // op on macOS (only the connect is gated), so this rule is the whole
            // door: the granted endpoint connects, all others EPERM.
            //
            // SBPL LIMITATION (honest): the `remote ip` HOST field accepts only
            // `*` or `localhost` — a literal remote IP is REJECTED by
            // `sandbox_init`. So:
            //   * a LOOPBACK grant (127.0.0.1 / ::1 / localhost) → `localhost:PORT`,
            //     precise host+port (the hermetic mock + the recommended local
            //     egress-proxy pattern, where a trusted host-side proxy pins the
            //     real upstream provider and the jail reaches only localhost).
            //   * a REMOTE-HOST grant → `*:PORT`, which SBPL can only pin by PORT,
            //     NOT host. This is a genuine degradation (any host on that port),
            //     so the host-pinned provider door for a REMOTE endpoint needs the
            //     local-proxy pattern above; direct-remote is port-scoped only.
            let (host, port) = endpoint
                .rsplit_once(':')
                .map(|(h, p)| (h, p))
                .unwrap_or((endpoint.as_str(), ""));
            let sbpl_host = if is_loopback(host) { "localhost" } else { "*" };
            p.push_str("(allow network-outbound (remote ip \"");
            p.push_str(sbpl_host);
            p.push(':');
            // The port is a bare integer; escape defensively anyway.
            for ch in port.chars() {
                if ch == '"' || ch == '\\' {
                    p.push('\\');
                }
                p.push(ch);
            }
            p.push_str("\"))\n");
        }
        // ── the HEAVY-BODY tier — each block emitted ONLY when its field is set,
        //    so an all-empty Confinement appends NOTHING here (byte-identical to
        //    the light jail). The allow-set mirrors homeserver.sb exactly. ──
        //
        // Writable subpaths (the db-dir door): read + write on each.
        for path in &c.write_paths {
            p.push_str("(allow file-read* (subpath \"");
            push_escaped(&mut p, path);
            p.push_str("\"))\n(allow file-write* (subpath \"");
            push_escaped(&mut p, path);
            p.push_str("\"))\n");
        }
        // Loopback listen (the firmament listen door): bind + inbound, LOOPBACK
        // ONLY. A non-loopback host is dropped (opens no inbound).
        for addr in &c.listen_addrs {
            let (host, port) = addr.rsplit_once(':').unwrap_or((addr.as_str(), ""));
            if !is_loopback(host) {
                continue;
            }
            for verb in ["network-bind", "network-inbound"] {
                p.push_str("(allow ");
                p.push_str(verb);
                p.push_str(" (local ip \"localhost:");
                push_escaped(&mut p, port);
                p.push_str("\"))\n");
            }
        }
        // The NAMED mach allow-list — one global-name per grant, NEVER a blanket.
        for svc in &c.mach_services {
            p.push_str("(allow mach-lookup (global-name \"");
            push_escaped(&mut p, svc);
            p.push_str("\"))\n");
        }
        // The system read/machinery bundle a heavy body needs to keep running.
        if c.system_reads {
            p.push_str(SYSTEM_MACHINERY);
            p.push_str(SYSTEM_READS_HEAD);
            if let Some(hb) = &c.homebrew_prefix {
                p.push_str("  (subpath \"");
                push_escaped(&mut p, hb);
                p.push_str("\")");
            }
            p.push_str(")\n");
        }
        // The one grain-image execve door: process-exec + file-read of the image.
        if let Some(img) = &c.exec_image {
            p.push_str("(allow process-exec (literal \"");
            push_escaped(&mut p, img);
            p.push_str("\"))\n(allow file-read* (literal \"");
            push_escaped(&mut p, img);
            p.push_str("\"))\n");
        }
        p
    }

    /// Push `s` into the SBPL profile, escaping the TinyScheme string-literal
    /// metacharacters (`"` and `\`). The shared escaper for every emitted literal.
    fn push_escaped(p: &mut String, s: &str) {
        for ch in s.chars() {
            if ch == '"' || ch == '\\' {
                p.push('\\');
            }
            p.push(ch);
        }
    }

    /// Process/thread MACHINERY a heavy body (rocksdb bg threads + tokio worker
    /// pool) needs — the `homeserver.sb` process block MINUS `process-exec`
    /// (which is the per-image `exec_image` door) and MINUS the `SELF`/db reads
    /// (their own grants). `sysctl-read`/`signal (target self)` overlap the base
    /// allow-set (duplicate SBPL allows are harmless).
    const SYSTEM_MACHINERY: &str = "\
(allow process-fork)\n\
(allow process-info-pidinfo)\n\
(allow process-info-setcontrol)\n\
(allow signal (target self))\n\
(allow sysctl-read)\n\
(allow system-socket)\n";

    /// The system READ bundle head — the dyld/libSystem/framework/char-device/etc
    /// reads a heavy body maps, mirroring `homeserver.sb`'s `file-read*` list
    /// (the `$HOMEBREW` subpath is appended from `homebrew_prefix`, then `)\n`).
    /// The leading `(literal "/")` is the dyld firmlink gotcha: without it the
    /// process SIGABRTs pre-main (firmlink resolution `opendir`s the root).
    const SYSTEM_READS_HEAD: &str = "\
(allow file-read-metadata)\n\
(allow file-read*\n\
  (literal \"/\")\n\
  (subpath \"/usr/lib\")\n\
  (subpath \"/System\")\n\
  (subpath \"/Library/Preferences/Logging\")\n\
  (literal \"/dev/null\")\n\
  (literal \"/dev/random\")\n\
  (literal \"/dev/urandom\")\n\
  (literal \"/dev/dtracehelper\")\n\
  (literal \"/etc\")\n\
  (literal \"/private/etc\")\n\
  (subpath \"/private/etc\")\n\
  (subpath \"/private/var/db/timezone\")";

    /// Whether `host` is a loopback the SBPL `localhost` token covers.
    fn is_loopback(host: &str) -> bool {
        matches!(host, "127.0.0.1" | "::1" | "localhost")
    }

    /// SELF-apply the Seatbelt profile to this (child) process.
    pub fn confine(c: &Confinement) -> Result<(), ConfineError> {
        let profile = build_profile(c);
        let cprofile =
            CString::new(profile).map_err(|e| ConfineError::SandboxInit(format!("nul: {e}")))?;
        let mut err: *mut c_char = ptr::null_mut();
        let rc = unsafe { sandbox_init(cprofile.as_ptr(), 0, &mut err) };
        if rc == 0 {
            Ok(())
        } else {
            let msg = if err.is_null() {
                "sandbox_init returned non-zero with no error string".to_string()
            } else {
                let m = unsafe { CStr::from_ptr(err) }
                    .to_string_lossy()
                    .into_owned();
                unsafe { sandbox_free_error(err) };
                m
            };
            Err(ConfineError::SandboxInit(msg))
        }
    }
}

// ───────────────────────────── Linux backend ────────────────────────────────
//
// Compiles on macOS as an unreachable cfg-stub (the module body is gated to
// `target_os = "linux"`); RUNS on Linux. The steps:
//   1. unshare(CLONE_NEWUSER|NEWNET|NEWNS|NEWPID) + a uid-map (root-in-namespace
//      maps to the real uid) — an EMPTY net namespace means no route anywhere.
//   2. prctl(PR_SET_NO_NEW_PRIVS, 1) — no setuid/fscaps escalation.
//   3. a default-deny seccomp-bpf allow-list (read/write/close/exit/… only) via
//      `seccompiler` — socket()/open()/execve() trap to EPERM/SIGSYS.
//   4. Landlock read rules for any granted read paths via `landlock`.
//   5. (close_all_but already ran in the shared path, keeping the control fd.)

#[cfg(target_os = "linux")]
mod linux {
    use super::provider_door::{self, AllowedEndpoint, DoorMode};
    use super::{ConfineError, Confinement};
    use std::io;
    use std::os::raw::c_int;
    use std::os::unix::io::RawFd;

    /// Apply the Linux confinement stack to this (child) process.
    ///
    /// Two shapes, decided purely from the granted `net_out`:
    ///   * `Sealed` (no grant) — the historical jail: empty net namespace + a
    ///     seccomp allow-list omitting `socket`. Fully net-sealed; deny-default.
    ///   * `ProviderNotify` (a grant) — the provider-only egress door: a trusted
    ///     supervisor (forked here, kept in the connected netns) mediates every
    ///     `connect`, admitting EXACTLY the granted endpoints and denying the rest.
    ///     The child's own net namespace still stays empty, so the ONLY reachable
    ///     endpoint is the one the supervisor establishes on its behalf.
    pub fn confine(c: &Confinement) -> Result<(), ConfineError> {
        match provider_door::door_mode(&c.net_out) {
            DoorMode::Sealed => confine_sealed(c),
            DoorMode::ProviderNotify => confine_with_provider_door(c),
        }
    }

    /// The fully net-sealed jail (no egress grant): unchanged deny-default floor.
    fn confine_sealed(c: &Confinement) -> Result<(), ConfineError> {
        unshare_namespaces()?;
        no_new_privs()?;
        apply_landlock(&c.read_paths)?;
        apply_seccomp_sealed()?;
        Ok(())
    }

    /// unshare USER+NET+NS+PID namespaces and write the uid/gid maps. An empty
    /// net namespace gives the child no network route at all (the net-cap denial).
    fn unshare_namespaces() -> Result<(), ConfineError> {
        use std::io::Write;
        // The real uid/gid to map root-in-namespace back to.
        let (uid, gid) = unsafe { (libc::getuid(), libc::getgid()) };
        let flags =
            libc::CLONE_NEWUSER | libc::CLONE_NEWNET | libc::CLONE_NEWNS | libc::CLONE_NEWPID;
        let rc = unsafe { libc::unshare(flags) };
        if rc != 0 {
            return Err(ConfineError::Linux(format!(
                "unshare failed: {}",
                std::io::Error::last_os_error()
            )));
        }
        // setgroups must be denied before writing gid_map in a userns.
        let _ = std::fs::write("/proc/self/setgroups", b"deny");
        std::fs::OpenOptions::new()
            .write(true)
            .open("/proc/self/uid_map")
            .and_then(|mut f| f.write_all(format!("0 {uid} 1\n").as_bytes()))
            .map_err(|e| ConfineError::Linux(format!("uid_map: {e}")))?;
        std::fs::OpenOptions::new()
            .write(true)
            .open("/proc/self/gid_map")
            .and_then(|mut f| f.write_all(format!("0 {gid} 1\n").as_bytes()))
            .map_err(|e| ConfineError::Linux(format!("gid_map: {e}")))?;
        Ok(())
    }

    /// prctl(PR_SET_NO_NEW_PRIVS, 1) — required before installing seccomp without
    /// CAP_SYS_ADMIN, and it blocks setuid/fscap privilege escalation.
    fn no_new_privs() -> Result<(), ConfineError> {
        let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
        if rc != 0 {
            return Err(ConfineError::Linux(format!(
                "prctl(NO_NEW_PRIVS): {}",
                std::io::Error::last_os_error()
            )));
        }
        Ok(())
    }

    /// Install a default-deny seccomp-bpf filter that allows only the syscalls a
    /// confined PD body needs (read/write/close/exit/sigreturn/…) and traps the
    /// rest (notably `socket`, `open`, `openat`, `execve`) to EPERM. Built with
    /// the `seccompiler` crate. This is the SEALED (no-egress-grant) filter — the
    /// provider-door filter is [`install_connect_notify_seccomp`] below.
    fn apply_seccomp_sealed() -> Result<(), ConfineError> {
        use seccompiler::{apply_filter, BpfProgram, SeccompAction, SeccompFilter, TargetArch};
        use std::collections::BTreeMap;

        #[cfg(target_arch = "x86_64")]
        let arch = TargetArch::x86_64;
        #[cfg(target_arch = "aarch64")]
        let arch = TargetArch::aarch64;

        // The allow-list: syscalls a bounded compute-over-the-socket PD needs.
        // Everything else → EPERM (errno 1). socket/open/openat/execve are NOT
        // listed, so they are denied — the ambient-authority drop.
        let allow: &[i64] = &[
            libc::SYS_read,
            libc::SYS_write,
            libc::SYS_close,
            libc::SYS_exit,
            libc::SYS_exit_group,
            libc::SYS_rt_sigreturn,
            libc::SYS_rt_sigprocmask,
            libc::SYS_sigaltstack,
            libc::SYS_brk,
            libc::SYS_mmap,
            libc::SYS_munmap,
            libc::SYS_mprotect,
            libc::SYS_futex,
            libc::SYS_nanosleep,
            libc::SYS_clock_nanosleep,
            libc::SYS_sched_yield,
            libc::SYS_getpid,
            libc::SYS_gettid,
            libc::SYS_getrandom,
            libc::SYS_madvise,
            libc::SYS_recvfrom,
            libc::SYS_sendto,
            libc::SYS_recvmsg,
            libc::SYS_sendmsg,
            libc::SYS_ppoll,
            libc::SYS_fcntl,
        ];
        let rules: BTreeMap<i64, Vec<_>> = allow.iter().map(|&n| (n, vec![])).collect();

        let filter = SeccompFilter::new(
            rules,
            SeccompAction::Errno(libc::EPERM as u32), // default: deny → EPERM
            SeccompAction::Allow,                     // matched (allow-listed) → allow
            arch,
        )
        .map_err(|e| ConfineError::Linux(format!("seccomp build: {e}")))?;

        let prog: BpfProgram = filter
            .try_into()
            .map_err(|e| ConfineError::Linux(format!("seccomp compile: {e}")))?;
        apply_filter(&prog).map_err(|e| ConfineError::Linux(format!("seccomp apply: {e}")))?;
        Ok(())
    }

    /// Restrict the filesystem with Landlock: deny everything, then re-grant
    /// read-only access to the explicitly-granted `read_paths` (the file-cap →
    /// OS-rule map). If Landlock is unavailable (old kernel), the empty net
    /// namespace + seccomp `open` denial already deny ambient FS authority, so
    /// we treat an ABI-unsupported result as best-effort (the deny still holds
    /// at the seccomp layer).
    fn apply_landlock(read_paths: &[String]) -> Result<(), ConfineError> {
        use landlock::{
            Access, AccessFs, Ruleset, RulesetAttr, RulesetCreatedAttr, RulesetStatus, ABI,
        };

        let abi = ABI::V1;
        let read_only = AccessFs::from_read(abi);
        let mut ruleset = Ruleset::default()
            .handle_access(AccessFs::from_all(abi))
            .map_err(|e| ConfineError::Linux(format!("landlock handle: {e}")))?
            .create()
            .map_err(|e| ConfineError::Linux(format!("landlock create: {e}")))?;

        for path in read_paths {
            // landlock 0.4.x: `PathBeneath::new` is infallible (returns the rule
            // directly, no longer a Result); only PathFd::new + add_rule can fail.
            let rule = landlock::PathBeneath::new(
                landlock::PathFd::new(path)
                    .map_err(|e| ConfineError::Linux(format!("landlock pathfd {path}: {e}")))?,
                read_only,
            );
            ruleset = ruleset
                .add_rule(rule)
                .map_err(|e| ConfineError::Linux(format!("landlock rule {path}: {e}")))?;
        }

        let status = ruleset
            .restrict_self()
            .map_err(|e| ConfineError::Linux(format!("landlock restrict: {e}")))?;
        // If the running kernel lacks Landlock, the restriction is a no-op here;
        // the seccomp `open` denial is the backstop, so this is not fatal.
        let _ = matches!(status.ruleset, RulesetStatus::NotEnforced);
        Ok(())
    }

    // ───────────────── the provider-only egress door (runtime) ──────────────────
    //
    // A seccomp USER_NOTIF filter on `connect(2)` supervised by a trusted, still-
    // connected sibling of the jailed body. Deny-default is structural: the jailed
    // body's net namespace stays empty, so the ONLY reachable endpoint is one the
    // supervisor establishes on its behalf after an EXACT `net_out` match. Every
    // other outcome (dead supervisor, unreadable child memory, unparsed sockaddr,
    // foreign address family) FAILS CLOSED — `EPERM`. The sole path to an open door
    // is the pure, unit-tested [`provider_door::admits`] check.

    /// Confine this child WITH the provider-only egress door. Forks a supervisor
    /// (kept in the connected netns), installs the connect-notify seccomp filter in
    /// the jailed body, and hands the notification listener to the supervisor. On
    /// return `Ok(())` the JAILED body runs; its `connect`s trap to the supervisor.
    fn confine_with_provider_door(c: &Confinement) -> Result<(), ConfineError> {
        // A socketpair to hand the seccomp listener fd from the jailed body up to
        // the supervisor. Created BEFORE the fork so both ends inherit it.
        let mut sv = [0 as RawFd; 2];
        if unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, sv.as_mut_ptr()) } != 0 {
            return Err(ConfineError::Linux(format!(
                "egress socketpair: {}",
                io::Error::last_os_error()
            )));
        }
        let (sv_super, sv_jailed) = (sv[0], sv[1]);

        // Resolve the grants in the SUPERVISOR-to-be BEFORE the fork/unshare, while
        // we still have real network (DNS) for any hostname grant.
        let allowed = resolve_allowed(&c.net_out);

        let pid = unsafe { libc::fork() };
        if pid < 0 {
            let e = io::Error::last_os_error();
            unsafe {
                libc::close(sv_super);
                libc::close(sv_jailed);
            }
            return Err(ConfineError::Linux(format!("egress supervisor fork: {e}")));
        }

        if pid > 0 {
            // ── SUPERVISOR: stays in the ORIGINAL (connected) net namespace; is the
            //    PARENT of the jailed body (so it may `process_vm_readv` it). It does
            //    NOT run the PD body; it services the notify listener, then reaps the
            //    jailed body and MIRRORS its exit code as its own (the kernel waits
            //    on THIS pid, so the jail verdict propagates through unchanged). ──
            unsafe {
                libc::close(sv_jailed);
                for fd in &c.endpoint_fds {
                    libc::close(*fd); // the supervisor never holds the Endpoint.
                }
            }
            let listener = unsafe { recv_fd(sv_super) };
            unsafe { libc::close(sv_super) };
            if let Some(listener) = listener {
                supervisor_loop(listener, pid, &allowed);
                unsafe { libc::close(listener) };
            }
            // Reap the jailed body and exit with ITS code (verdict passthrough).
            let mut status: c_int = 0;
            let code = unsafe {
                if libc::waitpid(pid, &mut status, 0) == pid && libc::WIFEXITED(status) {
                    libc::WEXITSTATUS(status)
                } else {
                    crate::process_kernel::CONFINE_FAILED_EXIT
                }
            };
            unsafe {
                let _ = io::Write::flush(&mut io::stdout());
                libc::_exit(code);
            }
        }

        // ── JAILED BODY (the real PD): empty net namespace + the connect-notify
        //    filter. It never gets a network route; its `connect`s are mediated. ──
        unsafe { libc::close(sv_super) };
        // Let the supervisor (our parent) trace us for the sockaddr read, even under
        // a restrictive Yama ptrace_scope.
        unsafe {
            libc::prctl(
                libc::PR_SET_PTRACER,
                libc::getppid() as libc::c_ulong,
                0,
                0,
                0,
            )
        };
        no_new_privs()?;
        unshare_namespaces()?;
        apply_landlock(&c.read_paths)?;
        let listener = install_connect_notify_seccomp()?;
        // Hand the listener to the supervisor, then drop OUR copies so the Endpoint
        // is again the single surviving non-std fd (the jailed body's fd invariant).
        let sent = unsafe { send_fd(sv_jailed, listener) };
        unsafe {
            libc::close(listener);
            libc::close(sv_jailed);
        }
        if !sent {
            return Err(ConfineError::Linux(
                "egress: handing the seccomp listener to the supervisor failed".into(),
            ));
        }
        Ok(())
    }

    /// Resolve `net_out` grants to the concrete `(ipv4, port)` set the supervisor
    /// admits: literal/loopback grants verbatim, hostname grants via `getaddrinfo`
    /// (the supervisor has real network). Runs in the supervisor before the fork.
    fn resolve_allowed(net_out: &[String]) -> Vec<([u8; 4], u16)> {
        let mut out = Vec::new();
        for ep in provider_door::expand_static_grants(net_out) {
            match ep {
                AllowedEndpoint::V4(ip, port) => out.push((ip, port)),
                AllowedEndpoint::Host(host, port) => resolve_host_ipv4(&host, port, &mut out),
            }
        }
        out
    }

    /// `getaddrinfo(host)` → each IPv4, paired with `port`, appended to `out`.
    fn resolve_host_ipv4(host: &str, port: u16, out: &mut Vec<([u8; 4], u16)>) {
        let Ok(chost) = std::ffi::CString::new(host) else {
            return;
        };
        let mut hints: libc::addrinfo = unsafe { std::mem::zeroed() };
        hints.ai_family = libc::AF_INET;
        hints.ai_socktype = libc::SOCK_STREAM;
        let mut res: *mut libc::addrinfo = std::ptr::null_mut();
        let rc = unsafe { libc::getaddrinfo(chost.as_ptr(), std::ptr::null(), &hints, &mut res) };
        if rc != 0 || res.is_null() {
            return;
        }
        let mut cur = res;
        while !cur.is_null() {
            let ai = unsafe { &*cur };
            if ai.ai_family == libc::AF_INET && !ai.ai_addr.is_null() {
                let sa = unsafe { &*(ai.ai_addr as *const libc::sockaddr_in) };
                out.push((sa.sin_addr.s_addr.to_ne_bytes(), port));
            }
            cur = ai.ai_next;
        }
        unsafe { libc::freeaddrinfo(res) };
    }

    /// Install the connect-notify seccomp filter and return the notification
    /// LISTENER fd (via `SECCOMP_FILTER_FLAG_NEW_LISTENER`). Allows the sealed
    /// allow-list PLUS `socket` + the socket-management syscalls, and routes
    /// `connect` to `USER_NOTIF`; everything else is `EPERM`.
    fn install_connect_notify_seccomp() -> Result<RawFd, ConfineError> {
        #[cfg(target_arch = "x86_64")]
        let arch = provider_door::AUDIT_ARCH_X86_64;
        #[cfg(target_arch = "aarch64")]
        let arch = provider_door::AUDIT_ARCH_AARCH64;

        // The sealed allow-list + what a mediated outbound connection needs. NB:
        // `connect` is NOT here — it is the notified syscall. `socket` IS (so the
        // child can create the fd the supervisor connects + injects over).
        let allow: &[i64] = &[
            libc::SYS_read,
            libc::SYS_write,
            libc::SYS_close,
            libc::SYS_exit,
            libc::SYS_exit_group,
            libc::SYS_rt_sigreturn,
            libc::SYS_rt_sigprocmask,
            libc::SYS_sigaltstack,
            libc::SYS_brk,
            libc::SYS_mmap,
            libc::SYS_munmap,
            libc::SYS_mprotect,
            libc::SYS_futex,
            libc::SYS_nanosleep,
            libc::SYS_clock_nanosleep,
            libc::SYS_sched_yield,
            libc::SYS_getpid,
            libc::SYS_gettid,
            libc::SYS_getrandom,
            libc::SYS_madvise,
            libc::SYS_recvfrom,
            libc::SYS_sendto,
            libc::SYS_recvmsg,
            libc::SYS_sendmsg,
            libc::SYS_ppoll,
            libc::SYS_fcntl,
            // The provider-door additions (present on x86_64 + aarch64):
            libc::SYS_socket,
            libc::SYS_getsockopt,
            libc::SYS_setsockopt,
            libc::SYS_getsockname,
            libc::SYS_getpeername,
            libc::SYS_shutdown,
            libc::SYS_epoll_create1,
            libc::SYS_epoll_ctl,
            libc::SYS_epoll_pwait,
            libc::SYS_pselect6,
        ];
        let insns = provider_door::build_connect_seccomp_bpf(arch, allow, libc::SYS_connect);
        let prog: Vec<libc::sock_filter> = insns
            .iter()
            .map(|i| libc::sock_filter {
                code: i.code,
                jt: i.jt,
                jf: i.jf,
                k: i.k,
            })
            .collect();
        let fprog = libc::sock_fprog {
            len: prog.len() as u16,
            filter: prog.as_ptr() as *mut libc::sock_filter,
        };
        let fd = unsafe {
            libc::syscall(
                libc::SYS_seccomp,
                libc::SECCOMP_SET_MODE_FILTER,
                libc::SECCOMP_FILTER_FLAG_NEW_LISTENER,
                &fprog as *const libc::sock_fprog,
            )
        };
        if fd < 0 {
            return Err(ConfineError::Linux(format!(
                "seccomp new_listener: {}",
                io::Error::last_os_error()
            )));
        }
        Ok(fd as RawFd)
    }

    // The seccomp-notify ioctls (computed from the asm-generic `_IOC` encoding used
    // by x86_64 + aarch64; `libc` ships the structs but not these request numbers).
    const SECCOMP_IOC_MAGIC: libc::c_ulong = b'!' as libc::c_ulong;
    const fn seccomp_ioc(dir: libc::c_ulong, nr: libc::c_ulong, size: usize) -> libc::c_ulong {
        (dir << 30) | (SECCOMP_IOC_MAGIC << 8) | nr | ((size as libc::c_ulong) << 16)
    }
    fn ioctl_notif_recv() -> libc::c_ulong {
        seccomp_ioc(3, 0, std::mem::size_of::<libc::seccomp_notif>())
    }
    fn ioctl_notif_send() -> libc::c_ulong {
        seccomp_ioc(3, 1, std::mem::size_of::<libc::seccomp_notif_resp>())
    }
    fn ioctl_notif_id_valid() -> libc::c_ulong {
        seccomp_ioc(1, 2, std::mem::size_of::<u64>())
    }
    fn ioctl_notif_addfd() -> libc::c_ulong {
        seccomp_ioc(1, 3, std::mem::size_of::<libc::seccomp_notif_addfd>())
    }

    /// THE SUPERVISOR NOTIFY LOOP — for each trapped `connect`, decide against the
    /// resolved grant set and answer. Runs in the connected netns; the jailed body
    /// is `child_pid`. Returns when the listener drains (the jailed body exited).
    fn supervisor_loop(listener: RawFd, child_pid: libc::pid_t, allowed: &[([u8; 4], u16)]) {
        loop {
            let mut notif: libc::seccomp_notif = unsafe { std::mem::zeroed() };
            let r = unsafe { libc::ioctl(listener, ioctl_notif_recv(), &mut notif) };
            if r != 0 {
                break; // the jailed body is gone (or a fatal listener error).
            }
            let (error, inject) = decide_connect(listener, &notif, child_pid, allowed);
            if let Some(src) = inject {
                // Replace the child's socket fd with the supervisor's connected one.
                let addfd = libc::seccomp_notif_addfd {
                    id: notif.id,
                    flags: libc::SECCOMP_ADDFD_FLAG_SETFD as u32,
                    srcfd: src as u32,
                    newfd: notif.data.args[0] as u32,
                    newfd_flags: 0,
                };
                let _ = unsafe { libc::ioctl(listener, ioctl_notif_addfd(), &addfd) };
                unsafe { libc::close(src) };
            }
            let resp = libc::seccomp_notif_resp {
                id: notif.id,
                val: 0,
                error, // 0 ⇒ success (val returned); negative errno ⇒ that failure.
                flags: 0,
            };
            let _ = unsafe { libc::ioctl(listener, ioctl_notif_send(), &resp) };
        }
    }

    /// Decide one trapped `connect`. Returns `(error, inject)`:
    ///   * `(0, Some(fd))` — admitted + the supervisor connected: inject `fd`, the
    ///     child's `connect` returns success on the now-connected socket.
    ///   * `(-errno, None)` — denied (`EPERM`) OR admitted-but-the-real-connect
    ///     failed (mirror that errno, e.g. `ECONNREFUSED`, so the jailed probe sees
    ///     the true reachability of the granted endpoint).
    /// Every non-admit path returns `-EPERM` — fail-closed.
    fn decide_connect(
        listener: RawFd,
        notif: &libc::seccomp_notif,
        child_pid: libc::pid_t,
        allowed: &[([u8; 4], u16)],
    ) -> (i32, Option<RawFd>) {
        let deny = (-libc::EPERM, None);
        if notif.data.nr as i64 != libc::SYS_connect {
            return deny; // only connect is notified; anything else is a bug → deny.
        }
        let addr_ptr = notif.data.args[1];
        let addr_len = notif.data.args[2] as usize;
        // Read the target sockaddr out of the child's address space, THEN confirm
        // the notification is still live (guards against a TOCTOU where the child
        // died/was reaped between the read and our decision).
        let Some((ip, port)) = read_child_sockaddr_in(child_pid, addr_ptr, addr_len) else {
            return deny;
        };
        let id = notif.id;
        if unsafe { libc::ioctl(listener, ioctl_notif_id_valid(), &id) } != 0 {
            return deny; // stale notification.
        }
        if !provider_door::admits(allowed, ip, port) {
            return deny; // not a granted endpoint.
        }
        // Admitted: establish the connection HERE (connected netns) on the child's
        // behalf. Success ⇒ inject the fd; a real failure ⇒ mirror its errno.
        let s = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
        if s < 0 {
            return deny;
        }
        let mut sa: libc::sockaddr_in = unsafe { std::mem::zeroed() };
        sa.sin_family = libc::AF_INET as libc::sa_family_t;
        sa.sin_port = port.to_be();
        sa.sin_addr.s_addr = u32::from_ne_bytes(ip);
        let rc = unsafe {
            libc::connect(
                s,
                &sa as *const _ as *const libc::sockaddr,
                std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
            )
        };
        if rc == 0 {
            (0, Some(s))
        } else {
            let e = io::Error::last_os_error()
                .raw_os_error()
                .unwrap_or(libc::EPERM);
            unsafe { libc::close(s) };
            (-e, None) // reachable but the peer failed the connect (e.g. refused).
        }
    }

    /// Read an `AF_INET` sockaddr from the child's memory at `ptr` and return its
    /// `(ipv4, port)`. `None` for any non-`AF_INET` family, a short read, or an
    /// unreadable address — each becomes a denial upstream (fail-closed).
    fn read_child_sockaddr_in(
        child_pid: libc::pid_t,
        ptr: u64,
        len: usize,
    ) -> Option<([u8; 4], u16)> {
        if len < std::mem::size_of::<libc::sockaddr_in>() {
            return None;
        }
        let mut buf = [0u8; 16]; // sizeof(sockaddr_in)
        let local = libc::iovec {
            iov_base: buf.as_mut_ptr() as *mut libc::c_void,
            iov_len: buf.len(),
        };
        let remote = libc::iovec {
            iov_base: ptr as *mut libc::c_void,
            iov_len: buf.len(),
        };
        let n = unsafe { libc::process_vm_readv(child_pid, &local, 1, &remote, 1, 0) };
        if n < buf.len() as isize {
            return None;
        }
        // sockaddr_in: family (u16, native) at [0..2], port (be) at [2..4], addr at [4..8].
        let family = u16::from_ne_bytes([buf[0], buf[1]]);
        if family != libc::AF_INET as u16 {
            return None;
        }
        let port = u16::from_be_bytes([buf[2], buf[3]]);
        let ip = [buf[4], buf[5], buf[6], buf[7]];
        Some((ip, port))
    }

    /// Send one fd to `sock` over `SCM_RIGHTS`. Returns whether it succeeded.
    unsafe fn send_fd(sock: RawFd, fd: RawFd) -> bool {
        let mut byte = [0u8; 1];
        let mut iov = libc::iovec {
            iov_base: byte.as_mut_ptr() as *mut libc::c_void,
            iov_len: 1,
        };
        let mut cbuf = [0u64; 8]; // 64 bytes, 8-byte aligned — room for one SCM_RIGHTS.
        let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
        msg.msg_iov = &mut iov;
        msg.msg_iovlen = 1;
        msg.msg_control = cbuf.as_mut_ptr() as *mut libc::c_void;
        msg.msg_controllen = unsafe { libc::CMSG_SPACE(std::mem::size_of::<c_int>() as u32) } as _;
        let cmsg = unsafe { libc::CMSG_FIRSTHDR(&msg) };
        if cmsg.is_null() {
            return false;
        }
        unsafe {
            (*cmsg).cmsg_level = libc::SOL_SOCKET;
            (*cmsg).cmsg_type = libc::SCM_RIGHTS;
            (*cmsg).cmsg_len = libc::CMSG_LEN(std::mem::size_of::<c_int>() as u32) as _;
            std::ptr::copy_nonoverlapping(
                &fd as *const c_int,
                libc::CMSG_DATA(cmsg) as *mut c_int,
                1,
            );
            libc::sendmsg(sock, &msg, 0) >= 0
        }
    }

    /// Receive one fd from `sock` over `SCM_RIGHTS`. `None` on any failure.
    unsafe fn recv_fd(sock: RawFd) -> Option<RawFd> {
        let mut byte = [0u8; 1];
        let mut iov = libc::iovec {
            iov_base: byte.as_mut_ptr() as *mut libc::c_void,
            iov_len: 1,
        };
        let mut cbuf = [0u64; 8];
        let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
        msg.msg_iov = &mut iov;
        msg.msg_iovlen = 1;
        msg.msg_control = cbuf.as_mut_ptr() as *mut libc::c_void;
        msg.msg_controllen = std::mem::size_of_val(&cbuf) as _;
        let n = unsafe { libc::recvmsg(sock, &mut msg, 0) };
        if n < 0 {
            return None;
        }
        let cmsg = unsafe { libc::CMSG_FIRSTHDR(&msg) };
        if cmsg.is_null() {
            return None;
        }
        unsafe {
            if (*cmsg).cmsg_level == libc::SOL_SOCKET && (*cmsg).cmsg_type == libc::SCM_RIGHTS {
                let mut fd: c_int = -1;
                std::ptr::copy_nonoverlapping(libc::CMSG_DATA(cmsg) as *const c_int, &mut fd, 1);
                if fd >= 0 {
                    return Some(fd);
                }
            }
        }
        None
    }
}

// ──────────────────────────────── tests ─────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn endpoint_only_keeps_just_the_control_fd() {
        let c = Confinement::endpoint_only(7);
        assert_eq!(c.endpoint_fds, vec![7]);
        assert!(c.read_paths.is_empty());
    }

    #[test]
    fn with_read_path_records_the_grant() {
        let c = Confinement::endpoint_only(4).with_read_path("/etc/hosts");
        assert_eq!(c.read_paths, vec!["/etc/hosts".to_string()]);
    }

    // The macOS profile builder is pure (no FFI) — exercise its text shape so a
    // profile regression is caught without invoking sandbox_init.
    #[cfg(target_os = "macos")]
    #[test]
    fn macos_profile_denies_by_default_and_grants_paths() {
        let c = Confinement::endpoint_only(3).with_read_path("/tmp/grant");
        let p = macos::build_profile(&c);
        assert!(p.contains("(deny default)"), "must be default-deny");
        assert!(!p.contains("network"), "must NOT allow network");
        assert!(!p.contains("process-exec"), "must NOT allow exec");
        assert!(
            p.contains("(subpath \"/tmp/grant\")"),
            "granted read path must appear"
        );
    }

    // A granted net_out endpoint becomes EXACTLY one network-outbound allow — the
    // structured egress socket door — while the profile stays default-deny/no-exec.
    #[cfg(target_os = "macos")]
    #[test]
    fn macos_profile_opens_exactly_the_granted_net_endpoint() {
        // No net grant → NO network allow at all (the Endpoint-only floor).
        let sealed = macos::build_profile(&Confinement::endpoint_only(3));
        assert!(!sealed.contains("network-outbound"), "sealed = no net door");
        // A LOOPBACK grant → precise host+port via the SBPL `localhost` token
        // (a literal remote IP is rejected by sandbox_init).
        let c = Confinement::endpoint_only(3).with_net_out("127.0.0.1:8080");
        let p = macos::build_profile(&c);
        assert!(p.contains("(deny default)"), "still default-deny");
        assert!(!p.contains("process-exec"), "still no exec");
        assert!(
            p.contains("(allow network-outbound (remote ip \"localhost:8080\"))"),
            "loopback grant → localhost:port network-outbound allow:\n{p}"
        );
        // A REMOTE-host grant → port-scoped (SBPL cannot pin a remote host).
        let c2 = Confinement::endpoint_only(3).with_net_out("api.example.com:443");
        let p2 = macos::build_profile(&c2);
        assert!(
            p2.contains("(allow network-outbound (remote ip \"*:443\"))"),
            "remote grant → port-scoped allow (SBPL host limitation):\n{p2}"
        );
    }

    // ── ADDITIVITY: an all-empty Confinement emits the EXACT light-jail profile.
    //    This pins byte-identity so the heavy-body tier can NEVER regress the
    //    light jail — if any heavy block leaks into the empty profile this fails.
    #[cfg(target_os = "macos")]
    #[test]
    fn all_empty_confinement_is_byte_identical_to_the_light_jail() {
        // The exact profile the LIGHT jail emitted before the heavy-body tier:
        // the deny-default prologue + the base keep-running allow-set, nothing
        // more. Reconstructed here so a drift in EITHER direction is caught.
        let baseline = "\
(version 1)\n\
(deny default)\n\
(allow file-read* (subpath \"/usr/lib\"))\n\
(allow file-read* (subpath \"/System/Library\"))\n\
(allow file-read* (subpath \"/Library/Apple\"))\n\
(allow file-read-metadata)\n\
(allow sysctl-read)\n\
(allow file-ioctl)\n\
(allow signal (target self))\n";
        // Default (all fields empty/false/None) — the additive floor.
        assert_eq!(
            macos::build_profile(&Confinement::default()),
            baseline,
            "an all-empty Confinement must emit the byte-identical light-jail profile"
        );
        // And endpoint_only(fd) (fds don't affect the profile text) matches too.
        assert_eq!(
            macos::build_profile(&Confinement::endpoint_only(9)),
            baseline
        );
    }

    // ── the HEAVY-BODY tier: the confined-homeserver profile mirrors the
    //    de-risked homeserver.sb — writable db subpath, loopback listen, the
    //    NAMED 10-service mach allow-list, the system read/machinery bundle, the
    //    ONE execve door — while staying default-deny and NEVER a blanket mach.
    #[cfg(target_os = "macos")]
    #[test]
    fn macos_heavy_body_profile_mirrors_homeserver_sb() {
        let c = Confinement::default()
            .with_system_reads()
            .with_homebrew_prefix("/opt/homebrew")
            .with_write_path("/private/var/folders/xx/db")
            .with_listen("127.0.0.1:*")
            .with_net_out("127.0.0.1:*")
            .with_homeserver_mach_defaults()
            .with_exec_image("/abs/deos-homeserver");
        let p = macos::build_profile(&c);

        // Still the deny-default floor.
        assert!(p.contains("(deny default)"));
        // The db-dir door: read AND write on the (canonical) subpath.
        assert!(p.contains("(allow file-read* (subpath \"/private/var/folders/xx/db\"))"));
        assert!(p.contains("(allow file-write* (subpath \"/private/var/folders/xx/db\"))"));
        // The loopback listen door: bind + inbound on localhost, loopback only.
        assert!(p.contains("(allow network-bind (local ip \"localhost:*\"))"));
        assert!(p.contains("(allow network-inbound (local ip \"localhost:*\"))"));
        // The self-probe outbound (reuses the existing net_out door).
        assert!(p.contains("(allow network-outbound (remote ip \"localhost:*\"))"));
        // The NAMED mach allow-list — all 10, and NEVER a blanket `(allow
        // mach-lookup)` with no global-name (the door is named, not broad).
        for svc in super::HOMESERVER_MACH_SERVICES {
            assert!(
                p.contains(&format!("(allow mach-lookup (global-name \"{svc}\"))")),
                "named mach service {svc} must appear"
            );
        }
        assert!(
            !p.contains("(allow mach-lookup)\n")
                && !p.contains("(allow mach-lookup (global-name \"*\"))"),
            "the mach allow-list must be NAMED, never a blanket"
        );
        // The system read bundle: the dyld firmlink root, the char devices, the
        // homebrew subpath.
        assert!(p.contains("(literal \"/\")"), "dyld firmlink root read");
        assert!(p.contains("(literal \"/dev/urandom\")"));
        assert!(p.contains("(subpath \"/opt/homebrew\")"), "homebrew reads");
        // The system machinery.
        assert!(p.contains("(allow process-fork)"));
        assert!(p.contains("(allow system-socket)"));
        // The ONE execve door: process-exec + file-read of EXACTLY the image.
        assert!(p.contains("(allow process-exec (literal \"/abs/deos-homeserver\"))"));
        assert!(p.contains("(allow file-read* (literal \"/abs/deos-homeserver\"))"));
        // No OTHER binary is exec-granted (exactly one process-exec literal).
        assert_eq!(
            p.matches("(allow process-exec (literal").count(),
            1,
            "exactly ONE image is exec-granted"
        );
    }

    // A listen grant for a NON-loopback host opens NO inbound (loopback-only door).
    #[cfg(target_os = "macos")]
    #[test]
    fn macos_non_loopback_listen_opens_no_inbound() {
        let c = Confinement::default().with_listen("0.0.0.0:8080");
        let p = macos::build_profile(&c);
        assert!(
            !p.contains("network-inbound"),
            "non-loopback listen = no inbound"
        );
        assert!(!p.contains("network-bind"), "non-loopback listen = no bind");
    }

    // ── the Linux provider-door PURE policy layer (unit-testable on any host) ──

    use super::provider_door::{self, AllowedEndpoint, DoorMode, AUDIT_ARCH_X86_64};

    #[test]
    fn door_mode_is_sealed_without_a_grant_and_notify_with_one() {
        assert_eq!(provider_door::door_mode(&[]), DoorMode::Sealed);
        assert_eq!(
            provider_door::door_mode(&["127.0.0.1:8899".to_string()]),
            DoorMode::ProviderNotify
        );
    }

    #[test]
    fn parse_grant_maps_ip_loopback_and_hostname() {
        assert_eq!(
            provider_door::parse_grant("127.0.0.1:8899"),
            Some(AllowedEndpoint::V4([127, 0, 0, 1], 8899))
        );
        assert_eq!(
            provider_door::parse_grant("localhost:80"),
            Some(AllowedEndpoint::V4([127, 0, 0, 1], 80))
        );
        assert_eq!(
            provider_door::parse_grant("api.anthropic.com:443"),
            Some(AllowedEndpoint::Host("api.anthropic.com".into(), 443))
        );
        // Malformed grants open NO door (never a wildcard).
        assert_eq!(provider_door::parse_grant("no-port"), None);
        assert_eq!(provider_door::parse_grant(":443"), None);
        assert_eq!(provider_door::parse_grant("host:notaport"), None);
    }

    #[test]
    fn expand_static_grants_skips_malformed_entries() {
        let g = provider_door::expand_static_grants(&[
            "127.0.0.1:8899".into(),
            "garbage".into(),
            "localhost:1".into(),
        ]);
        assert_eq!(
            g,
            vec![
                AllowedEndpoint::V4([127, 0, 0, 1], 8899),
                AllowedEndpoint::V4([127, 0, 0, 1], 1),
            ]
        );
    }

    // THE FAIL-OPEN-CRITICAL check: EXACTLY the granted (ip, port) opens; a sibling
    // port, a sibling host, and the empty grant set each stay CLOSED.
    #[test]
    fn admits_opens_exactly_the_granted_endpoint() {
        let allowed = [([127, 0, 0, 1], 8899u16)];
        assert!(provider_door::admits(&allowed, [127, 0, 0, 1], 8899));
        assert!(
            !provider_door::admits(&allowed, [127, 0, 0, 1], 9999),
            "a different port is denied"
        );
        assert!(
            !provider_door::admits(&allowed, [1, 1, 1, 1], 8899),
            "a different host is denied"
        );
        assert!(
            !provider_door::admits(&[], [127, 0, 0, 1], 8899),
            "no grant ⇒ nothing admitted (deny-default)"
        );
    }

    // The connect-notify cBPF program: guards the arch, ALLOWs the allow-list,
    // routes connect → USER_NOTIF, and defaults to EPERM — the exact door shape.
    #[test]
    fn connect_seccomp_bpf_has_the_right_shape() {
        let allow: &[i64] = &[0x1122, 0x3344]; // stand-in nrs (socket, read, …).
        let notify_nr: i64 = 0x2a; // stand-in connect nr.
        let prog = provider_door::build_connect_seccomp_bpf(AUDIT_ARCH_X86_64, allow, notify_nr);
        // [0] loads arch (offset 4), [1] guards it against the arch token.
        assert_eq!(prog[0].code, 0x20);
        assert_eq!(prog[0].k, 4, "first insn loads seccomp_data.arch");
        assert_eq!(prog[1].k, AUDIT_ARCH_X86_64, "arch is pinned");
        // [2] loads nr (offset 0); a comparison exists for the connect nr.
        assert_eq!(prog[2].k, 0, "third insn loads seccomp_data.nr");
        assert!(
            prog.iter().any(|i| i.k == notify_nr as u32),
            "connect nr is compared"
        );
        assert!(
            prog.iter().any(|i| i.k == 0x1122),
            "an allow nr is compared"
        );
        // The three terminal returns exist: EPERM (deny-default), ALLOW, USER_NOTIF.
        assert!(
            prog.iter().any(|i| i.code == 0x06 && i.k == 0x0005_0001),
            "deny=EPERM"
        );
        assert!(
            prog.iter().any(|i| i.code == 0x06 && i.k == 0x7fff_0000),
            "ALLOW"
        );
        assert!(
            prog.iter().any(|i| i.code == 0x06 && i.k == 0x7fc0_0000),
            "USER_NOTIF (connect traps to the supervisor)"
        );
    }
}
