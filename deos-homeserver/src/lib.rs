//! deos-homeserver — continuwuity embedded as a library, the grain body for the
//! self-hosted membrane (see `docs/deos/GRAIN-HOMESERVER.md`).
//!
//! The embed seam (`conduwuit::run_with_args(&Args)`) boots a real Matrix
//! homeserver in-process. This crate wraps that into an [`EmbeddedHomeserver`]
//! (loopback config + readiness poll) so a dregg grain can host the membrane its
//! co-driven cards ride, instead of an external Docker Conduit.
//!
//! Step 1 (this crate): boot it in-process + prove it serves the CS API a Matrix
//! client needs. Step 2/3 (design-first): the confined spawn + the one
//! `grant_read_write` firmament door for the RocksDB dir.
//!
//! # The boot seam
//!
//! `conduwuit::run_with_args(&Args)` (the main crate's `[lib]`) builds the tokio
//! runtime, constructs the internal `Server` (an `Arc<conduwuit_core::Server>`
//! it keeps private), spawns the signal handler, and `block_on`s the axum HTTP
//! server until shutdown. It therefore **blocks the calling thread** until the
//! server stops, and it does **not** hand back the `Arc<Server>` — so there is
//! no in-process shutdown handle reachable through this API.
//!
//! # Shutdown (step-1 decision: drop the thread)
//!
//! Because `run_with_args` owns the `Server` internally and never returns it, no
//! `shutdown()`/signal handle is cleanly reachable. Sending a signal would be
//! process-wide (it would take down the caller too), which is wrong for an
//! embedded grain body. For step 1 we therefore **drop the background thread**
//! on `Drop` and rely on a **unique temp dir + unique loopback port per
//! instance** so there is no RocksDB lock collision between instances or across
//! test runs. The daemon thread is reaped when the process exits. A real
//! in-process shutdown (reaching the `Arc<Server>` and calling its shutdown, or
//! forking a small upstream patch that returns the handle) is a step-2/3
//! concern, wired alongside the confined spawn and the `grant_read_write` door.
//!
//! Note: `run_with_args` calls `rustls::crypto::*::default_provider()
//! .install_default().expect(...)`, a **process-global** one-shot. Booting a
//! second `EmbeddedHomeserver` in the same process would panic that background
//! thread on the second install. Step 1 boots exactly one server per process.
//!
//! This wrapper is std-only (no reqwest/tempfile in the grain body): a manual
//! temp tree and a raw-TCP readiness probe keep the embedded homeserver's direct
//! dependency surface to just `conduwuit` + `tokio`/`anyhow`.

use std::{
    io::{Read, Write},
    net::{Ipv4Addr, TcpListener, TcpStream},
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    thread::JoinHandle,
    time::{Duration, Instant},
};

use anyhow::{Context, Result, anyhow};

/// A real continuwuity Matrix homeserver booted in-process on loopback.
///
/// [`EmbeddedHomeserver::start`] writes a loopback config TOML into a fresh temp
/// directory (with a unique RocksDB `database_path`), then boots
/// `conduwuit::run_with_args` on a background thread (it blocks). Use
/// [`EmbeddedHomeserver::wait_until_ready`] to block until the CS API answers,
/// then [`EmbeddedHomeserver::base_url`] for the client-server API root.
pub struct EmbeddedHomeserver {
    base_url: String,
    port: u16,
    /// The RocksDB data directory (the future `grant_read_write` firmament door
    /// targets exactly this path).
    data_dir: PathBuf,
    /// Root temp tree, removed on drop.
    temp_root: PathBuf,
    /// The boot thread. `run_with_args` blocks on it until process exit; we drop
    /// it (see the module-level shutdown note).
    _thread: Option<JoinHandle<()>>,
}

impl EmbeddedHomeserver {
    /// Boot a fresh homeserver on loopback with open registration, no
    /// federation. `server_name` becomes the homeserver name (user ids look
    /// like `@alice:{server_name}`); pass e.g. `"localhost"`.
    pub fn start(server_name: &str) -> Result<Self> {
        // Unique temp tree per instance (no tempfile dep) — pid + a process-local
        // counter avoids collision across instances and concurrent test runs.
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let uniq = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_root =
            std::env::temp_dir().join(format!("deos-homeserver-{}-{}", std::process::id(), uniq));
        std::fs::create_dir_all(&temp_root).context("create temp root for homeserver")?;

        // Unique RocksDB dir per instance — no lock collision across instances
        // or runs. This is the path the future grant_read_write door governs.
        let data_dir = temp_root.join("db");
        std::fs::create_dir_all(&data_dir).context("create db dir")?;

        // A free loopback port, chosen by binding :0 and reading it back, then
        // released so continuwuity can bind it itself. (Step 2 replaces this with
        // the with_fds pre-bound-listener door; for step 1 the race window is
        // negligible on loopback.)
        let port = {
            let l = TcpListener::bind((Ipv4Addr::LOCALHOST, 0))
                .context("probe a free loopback port")?;
            l.local_addr().context("read probed port")?.port()
        };

        let config_toml = format!(
            concat!(
                "[global]\n",
                "server_name = \"{server_name}\"\n",
                "address = [\"127.0.0.1\"]\n",
                "port = {port}\n",
                "database_path = \"{db}\"\n",
                "allow_registration = true\n",
                // Open registration without a token requires this explicit
                // acknowledgement, else the register UIAA session offers no
                // completable flow (register.rs::create_registration_uiaa_session
                // only pushes the m.login.dummy flow when this is set).
                "yes_i_am_very_very_sure_i_want_an_open_registration_server_prone_to_abuse = true\n",
                // On a fresh DB continuwuity enters "first-run" mode: the first
                // registration is FORCED to a single-use, randomly-generated
                // registration token (surfaced only in logs) and open/dummy
                // registration is refused (firstrun/mod.rs, registration_tokens
                // validate_token). Disabling first-run mode (the same switch the
                // Matrix Complement test-suite uses) lets the first user register
                // through the normal open m.login.dummy flow.
                "force_disable_first_run_mode = true\n",
                "allow_federation = false\n",
                "listening = true\n",
                // Keep the trans-flag displayname suffix out of round-trip
                // assertions; empty = no suffix.
                "new_user_displayname_suffix = \"\"\n",
            ),
            server_name = server_name,
            port = port,
            db = data_dir.display(),
        );

        let config_path = temp_root.join("continuwuity.toml");
        std::fs::write(&config_path, config_toml).context("write homeserver config")?;

        let thread = std::thread::Builder::new()
            .name("deos-homeserver".into())
            .spawn(move || {
                // run_with_args blocks until shutdown. Args has all-pub fields.
                let args = conduwuit::Args {
                    config: Some(vec![config_path]),
                    option: Vec::new(),
                    maintenance: false,
                    // conduwuit's default features include `console`, so this
                    // field is present in Args. (We cannot `cfg` on the dep's
                    // feature from here, so it is set unconditionally to match
                    // the pinned default-feature build.)
                    console: false,
                    execute: Vec::new(),
                    test: Vec::new(),
                    worker_threads: default_worker_threads(),
                    global_event_interval: 192,
                    kernel_event_interval: 512,
                    kernel_events_per_tick: 512,
                    worker_histogram_interval: 25,
                    worker_histogram_buckets: 20,
                    worker_affinity: true,
                    gc_on_park: None,
                    gc_muzzy: None,
                };
                if let Err(e) = conduwuit::run_with_args(&args) {
                    eprintln!("deos-homeserver: run_with_args exited: {e}");
                }
            })
            .context("spawn homeserver thread")?;

        Ok(Self {
            base_url: format!("http://127.0.0.1:{port}"),
            port,
            data_dir,
            temp_root,
            _thread: Some(thread),
        })
    }

    /// The client-server API root, e.g. `http://127.0.0.1:PORT`.
    #[must_use]
    pub fn base_url(&self) -> &str {
        &self.base_url
    }

    /// The loopback port the homeserver bound (the future `with_fds` listen-door
    /// target).
    #[must_use]
    pub fn port(&self) -> u16 {
        self.port
    }

    /// The RocksDB data directory (the future `grant_read_write` door target).
    #[must_use]
    pub fn data_dir(&self) -> &Path {
        &self.data_dir
    }

    /// Block until the CS API answers `GET /_matrix/client/versions` with HTTP
    /// 200, or `timeout` elapses. Returns the base URL on success. Uses a raw
    /// TCP HTTP/1.0 probe so the grain body carries no HTTP client dependency.
    pub fn wait_until_ready(&self, timeout: Duration) -> Result<&str> {
        let deadline = Instant::now() + timeout;
        let mut last_err: Option<String> = None;
        while Instant::now() < deadline {
            match probe_versions_200(self.port) {
                Ok(true) => return Ok(&self.base_url),
                Ok(false) => last_err = Some("non-200".into()),
                Err(e) => last_err = Some(e.to_string()),
            }
            std::thread::sleep(Duration::from_millis(100));
        }
        Err(anyhow!(
            "homeserver not ready within {timeout:?} (last: {})",
            last_err.as_deref().unwrap_or("no response")
        ))
    }
}

impl Drop for EmbeddedHomeserver {
    fn drop(&mut self) {
        // Drop the thread (see module shutdown note) and remove the temp tree.
        // RocksDB still holds the dir until the process exits; best-effort clean.
        let _ = std::fs::remove_dir_all(&self.temp_root);
    }
}

/// Raw-TCP HTTP/1.0 probe of `GET /_matrix/client/versions`; true iff the status
/// line reports 200.
fn probe_versions_200(port: u16) -> Result<bool> {
    let mut stream = TcpStream::connect_timeout(
        &(Ipv4Addr::LOCALHOST, port).into(),
        Duration::from_millis(500),
    )?;
    stream.set_read_timeout(Some(Duration::from_secs(2)))?;
    stream.set_write_timeout(Some(Duration::from_secs(2)))?;
    stream.write_all(
        b"GET /_matrix/client/versions HTTP/1.0\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n",
    )?;
    let mut buf = Vec::with_capacity(256);
    // We only need the status line; read enough of the head.
    let mut chunk = [0u8; 512];
    loop {
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&chunk[..n]);
        if buf.windows(4).any(|w| w == b"\r\n\r\n") || buf.len() > 4096 {
            break;
        }
    }
    let head = String::from_utf8_lossy(&buf);
    Ok(head.starts_with("HTTP/1.1 200") || head.starts_with("HTTP/1.0 200"))
}

fn default_worker_threads() -> usize {
    std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(2)
        .max(2)
}
