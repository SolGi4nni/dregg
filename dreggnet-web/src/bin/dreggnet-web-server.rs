//! # `dreggnet-web-server` — the public-demo server entrypoint.
//!
//! The ~15-line-core unblocker to a public demo at `demo.dregg.net`: it takes the merged
//! [`dreggnet_web::make_app`] app (the games + feature-surface catalog + the seeded no-cheat
//! Descent leaderboard) and SERVES it — binds a `TcpListener`, `axum::serve`s, and shuts down
//! gracefully on ctrl-c. A stranger opens the URL and plays the games + independently re-verifies
//! the leaderboard by replay — no node, no testnet, no 45-min prover.
//!
//! ## Configuration
//! - bind address: `--bind <addr>` flag, else `DREGGNET_WEB_BIND` env, else `127.0.0.1:8787`;
//! - persistence: `DATABASE_URL` env (a sqlite path / `sqlite:` url) makes the Descent leaderboard
//!   durable — submitted runs survive a restart, re-verified by replay on boot; unset → in-RAM;
//! - sessions: `DREGGNET_WEB_SESSION_DIR` env (a directory) makes the live game sessions durable —
//!   each session's move-log persists there and resumes on boot by replay (a tampered log refuses
//!   to reopen, fail-closed); unset → in-memory only (a restart drops in-progress sessions);
//! - session lifecycle: `DREGGNET_WEB_MAX_SESSIONS` (live sessions per offering, LRU eviction),
//!   `DREGGNET_WEB_SESSION_TTL_SECS` (idle eviction; a 60s interval task + on-open sweeps drive
//!   it), `DREGGNET_WEB_OPENS_PER_USER` and `DREGGNET_WEB_MIN_OPEN_INTERVAL_SECS` (per-identity
//!   open quota / rate — advisory against a forged cookie identity; capacity + TTL are the real
//!   backstops). All unset → today's unbounded behavior. With a session dir, eviction is lossless
//!   (evicted sessions resume from the store on next touch); without one, arming any limit opts
//!   into honest lossy shedding of the coldest sessions;
//! - Telegram Mini App: `TELEGRAM_BOT_TOKEN` set (on the FUNNEL unit — the same variable the bot
//!   unit carries) mounts the `/tg` surface: initData HMAC-validated Telegram identities landing
//!   turns with verified `Signed` provenance (`dreggnet_web::telegram_miniapp`,
//!   docs/TELEGRAM-MINIAPP-DESIGN.md). Set an explicit `TELEGRAM_BOT_SECRET` (64 hex) in BOTH the
//!   bot and web units so a token rotation does not rotate every derived identity — both
//!   processes resolve the secret through the ONE `master_secret_from_env`.
//!   `TELEGRAM_INITDATA_MAX_AGE_SECS` tunes the initData freshness window (default 86400). Token
//!   unset → the `/tg` routes are not mounted and the catalog serves exactly as before;
//! - log level: the standard `RUST_LOG` env (`tracing_subscriber` env-filter), default `info`.
//!
//! ## Honest scope (the deploy scout's Phase-0)
//! DEMO-READY here: the standalone web server — the games, the do-once feature surfaces, and the
//! no-cheat-by-REPLAY Descent leaderboard + stranger-run verify + an HTTP run-ingest
//! (`POST /descent/submit`), all node-free (verification is in-process re-execution). The Descent
//! leaderboard is DURABLE over sqlite (`DATABASE_URL`), re-verified on boot; the live game sessions
//! are DURABLE over a move-log file store (`DREGGNET_WEB_SESSION_DIR`), resumed on boot by replay
//! (unset → ephemeral, a restart drops them). NAMED (ops / ember-gated): a fronting
//! Caddy for TLS / rate-limit / CORS (external); the unsigned `dregg_user` cookie for identity
//! (auth). See [`dreggnet_web::make_app`].

use std::net::SocketAddr;
use std::time::Duration;

use dreggnet_web::make_app_parts;
use tracing_subscriber::EnvFilter;

/// The bind address the demo server listens on when nothing else is configured.
const DEFAULT_BIND: &str = "127.0.0.1:8787";

/// The loopback address the SEPARATE metrics listener binds when nothing else is configured — a
/// distinct port from the main app so a public funnel of the demo never exposes `/metrics`.
const DEFAULT_METRICS_BIND: &str = "127.0.0.1:9790";

#[tokio::main]
async fn main() {
    // Structured logging — `RUST_LOG` selects the level (default `info`).
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")),
        )
        .init();

    let bind = resolve_bind();
    let addr: SocketAddr = match bind.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!(%bind, error = %e, "invalid bind address");
            std::process::exit(2);
        }
    };

    // The merged public-demo app: games + feature surfaces + the seeded no-cheat leaderboard —
    // plus the catalog handle, for the periodic session-lifecycle sweep below.
    let (app, catalog) = make_app_parts();

    // THE PERIODIC LIFECYCLE SWEEP — the timer half of the sweep design (documented on
    // `CatalogState::sweep`): the host already sweeps opportunistically on every fresh open, so
    // this interval task only covers the NO-TRAFFIC case (idle sessions past their TTL release
    // memory without waiting for the next visitor). A no-op unless a session policy with a TTL
    // is armed (`DREGGNET_WEB_SESSION_TTL_SECS`).
    {
        let catalog = catalog.clone();
        tokio::spawn(async move {
            let mut tick = tokio::time::interval(Duration::from_secs(60));
            tick.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
            loop {
                tick.tick().await;
                // `sweep` ships a job to the host's owning thread; run it off the async worker.
                let catalog = catalog.clone();
                let report = tokio::task::spawn_blocking(move || catalog.sweep()).await;
                match report {
                    Ok(r) if !r.evicted.is_empty() => tracing::info!(
                        evicted = r.evicted.len(),
                        retained_unpersisted = r.retained_unpersisted.len(),
                        "session-lifecycle sweep evicted idle sessions"
                    ),
                    Ok(_) => {}
                    Err(e) => tracing::warn!(error = %e, "session-lifecycle sweep task failed"),
                }
            }
        });
    }

    // THE METRICS LISTENER — a SEPARATE loopback server for `GET /metrics`, deliberately NOT on
    // the main (funnel-able) port, so a public `tailscale funnel` of the demo can never expose the
    // operational counters. Default `127.0.0.1:9790` (loopback); override with
    // `DREGGNET_WEB_METRICS_BIND`. Prometheus scrapes THIS port. A bind failure here is non-fatal —
    // the demo serves fine without a scrape target; we log and carry on.
    {
        let metrics_bind = std::env::var("DREGGNET_WEB_METRICS_BIND")
            .unwrap_or_else(|_| DEFAULT_METRICS_BIND.to_string());
        match metrics_bind.parse::<SocketAddr>() {
            Ok(maddr) => match tokio::net::TcpListener::bind(maddr).await {
                Ok(mlistener) => {
                    tracing::info!(%maddr, "metrics listener up (loopback) — GET /metrics");
                    tokio::spawn(async move {
                        if let Err(e) = axum::serve(mlistener, dreggnet_web::metrics_app()).await {
                            tracing::error!(error = %e, "metrics server error");
                        }
                    });
                }
                Err(e) => tracing::error!(
                    %maddr, error = %e,
                    "failed to bind the metrics listener — /metrics unavailable, demo continues"
                ),
            },
            Err(e) => tracing::error!(
                %metrics_bind, error = %e,
                "invalid DREGGNET_WEB_METRICS_BIND — /metrics unavailable, demo continues"
            ),
        }
    }

    let listener = match tokio::net::TcpListener::bind(addr).await {
        Ok(l) => l,
        Err(e) => {
            tracing::error!(%addr, error = %e, "failed to bind — is the port in use?");
            std::process::exit(1);
        }
    };

    tracing::info!(
        %addr,
        "DreggNet Cloud demo server up — GET / (landing) · /offerings (catalog) · \
         /descent/leaderboard (no-cheat board) · /health"
    );

    if let Err(e) = axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await
    {
        tracing::error!(error = %e, "server error");
        std::process::exit(1);
    }
    tracing::info!("server shut down gracefully");
}

/// Resolve the bind address: `--bind <addr>` flag > `DREGGNET_WEB_BIND` env > [`DEFAULT_BIND`].
fn resolve_bind() -> String {
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--bind" => {
                if let Some(v) = args.next() {
                    return v;
                }
            }
            other => {
                if let Some(v) = other.strip_prefix("--bind=") {
                    return v.to_string();
                }
            }
        }
    }
    std::env::var("DREGGNET_WEB_BIND").unwrap_or_else(|_| DEFAULT_BIND.to_string())
}

/// Complete on ctrl-c — hands `axum::serve` its graceful-shutdown trigger.
async fn shutdown_signal() {
    let _ = tokio::signal::ctrl_c().await;
    tracing::info!("received ctrl-c — shutting down");
}
