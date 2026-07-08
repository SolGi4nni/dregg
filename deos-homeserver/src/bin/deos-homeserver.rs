//! `deos-homeserver` — run the embedded continuwuity homeserver as a standalone
//! SERVER PROCESS the deos-matrix / starbridge matrix-rust-sdk clients dial over
//! HTTP.
//!
//! This is the "our-homeserver-as-a-subprocess" shape for the card-carry membrane
//! (Pillar 3 of `docs/deos/GRAIN-HOMESERVER.md`): the deos-matrix live tests and
//! the starbridge one-process card-fork loop are separate binaries in a separate
//! (rolling-nightly) workspace; they cannot link this (1.96.1, heavy git-pinned)
//! crate, and `run_with_args` installs a PROCESS-GLOBAL rustls provider (one server
//! per process). So the natural integration is two processes talking HTTP: this bin
//! is the server, the tests are the clients, and `scripts/card-carry-local.sh` is
//! the local-binary dual of `deos-matrix/scripts/live-test.sh` (Docker Conduit).
//!
//! Protocol: boot [`EmbeddedHomeserver`], wait until the CS API answers, print a
//! single parseable line `READY <base_url>` to stdout (flushed), then STAY UP,
//! blocking until SIGTERM/SIGINT — at which point it drops the homeserver (temp-dir
//! cleanup, see the lib shutdown note) and exits.
//!
//! `server_name` is taken from argv[1] or `$DEOS_HS_SERVER_NAME`, default
//! `localhost` (user ids look like `@alice:localhost`).

use std::{io::Write, time::Duration};

use deos_homeserver::EmbeddedHomeserver;

fn main() -> anyhow::Result<()> {
    let server_name = std::env::args()
        .nth(1)
        .or_else(|| std::env::var("DEOS_HS_SERVER_NAME").ok())
        .unwrap_or_else(|| "localhost".to_string());

    let ready_timeout = std::env::var("DEOS_HS_READY_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(120);

    eprintln!("deos-homeserver: booting (server_name={server_name})");
    let hs = EmbeddedHomeserver::start(&server_name)?;
    let base = hs
        .wait_until_ready(Duration::from_secs(ready_timeout))?
        .to_string();

    // The one parseable contract line the harness greps for. Flush so a
    // line-buffered reader (bash `read`) sees it immediately.
    println!("READY {base}");
    std::io::stdout().flush().ok();
    eprintln!(
        "deos-homeserver: READY base_url={base} port={} data_dir={}",
        hs.port(),
        hs.data_dir().display()
    );

    // Stay up until a termination signal, then drop(hs) for best-effort cleanup.
    // A small current-thread tokio runtime handles the signals; continuwuity's own
    // internal runtime (on its boot thread) is separate. tokio's signal handling is
    // process-global-registry based, so both can observe the same signal — either
    // shutting down is fine, the process exits.
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    rt.block_on(async {
        use tokio::signal::unix::{SignalKind, signal};
        let mut term = signal(SignalKind::terminate()).expect("install SIGTERM handler");
        tokio::select! {
            _ = tokio::signal::ctrl_c() => eprintln!("deos-homeserver: SIGINT received"),
            _ = term.recv() => eprintln!("deos-homeserver: SIGTERM received"),
        }
    });

    eprintln!("deos-homeserver: shutting down");
    drop(hs);
    Ok(())
}
