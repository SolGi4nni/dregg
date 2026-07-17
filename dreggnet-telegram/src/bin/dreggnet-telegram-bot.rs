//! # `dreggnet-telegram-bot` — the RUNNING Telegram bot over the shared DreggNet catalog.
//!
//! The whole offering stack (the 18-offering shared catalog, the real substrate turns, the
//! replay verifier) is the committed library; this bin is only the process shell:
//!
//! 1. token from `TELEGRAM_BOT_TOKEN` (checked live against `getMe` at startup);
//! 2. a durable per-`(offering, chat)` session store (`FileResumeStore` move-logs) under
//!    `TELEGRAM_SESSION_DIR` — a restart RESUMES every session by replay;
//! 3. the `getUpdates` long-poll loop routing button callbacks + text commands through
//!    [`TelegramHost::press`]/[`TelegramHost::open`], editing/sending the surface replies.
//!
//! ## Environment
//! - `TELEGRAM_BOT_TOKEN` (**required**) — the BotFather token. Ops-gated: without it the bin
//!   exits with a clear message (there is nothing honest a Telegram bot can do without one).
//! - `TELEGRAM_BOT_SECRET` (optional, 64 hex chars) — the identity-derivation master secret.
//!   Default: BLAKE3-derived from the token. ⚠ Every user's dregg identity derives from this:
//!   rotating the token (or setting a different secret) REMAPS all identities. Pin it explicitly
//!   for any deployment that expects to rotate tokens.
//! - `TELEGRAM_SESSION_DIR` (optional) — the durable session-store dir. Default:
//!   `$HOME/.local/state/dregg-telegram/sessions` (or `./dregg-telegram-sessions` without HOME).
//! - `TELEGRAM_COUNCIL_UIDS` (optional) — comma-separated Telegram user ids registered as the
//!   council electorate (their derived identities can really vote).
//! - `TELEGRAM_API_BASE` (optional) — override the Bot API host (a self-hosted server).
//! - `TELEGRAM_WEBAPP_BASE` (optional) — the public HTTPS base the Mini App (`dreggnet-web`'s
//!   `/tg` routes) is served from. Default: `https://hbox-dregg.skunk-emperor.ts.net` (the hbox
//!   funnel). DMs get "Play in the app" `web_app` buttons + the `/play` menu deep-linking it.
//!
//! Deploy: `deploy/telegram/dregg-telegram-bot.service` + `deploy/telegram/RUNBOOK-TELEGRAM.md`.

use std::path::PathBuf;

use dreggnet_telegram::host::TelegramHost;
use dreggnet_telegram::reqwest_transport::ReqwestHttpPost;
use dreggnet_telegram::runtime::{BotApi, durable_telegram_host, run_update_loop};
use dreggnet_telegram::transport::RawBotApi;

/// The concrete transport the running bot presents surfaces through.
type LiveTransport = RawBotApi<ReqwestHttpPost>;

fn main() {
    // 1. The token — ops-gated; exit honestly without it.
    let token = match std::env::var("TELEGRAM_BOT_TOKEN") {
        Ok(t) if !t.trim().is_empty() => t.trim().to_string(),
        _ => {
            eprintln!(
                "TELEGRAM_BOT_TOKEN is not set. Get a token from @BotFather and export it \
                 (see deploy/telegram/RUNBOOK-TELEGRAM.md). Exiting."
            );
            std::process::exit(2);
        }
    };

    // 2. The identity master secret — explicit hex, or derived from the token (see module doc).
    //    Resolved through the ONE lib impl (`cipherclerk::master_secret_from_env`) the web Mini
    //    App validator also calls — parity by construction, never by convention.
    let bot_secret = match dreggnet_telegram::cipherclerk::master_secret_from_env(&token) {
        Ok(s) => s,
        Err(why) => {
            eprintln!("TELEGRAM_BOT_SECRET is malformed: {why}");
            std::process::exit(2);
        }
    };

    // 3. The durable session dir (created up front — the offset file lives beside the logs).
    let session_dir = std::env::var("TELEGRAM_SESSION_DIR")
        .ok()
        .filter(|d| !d.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| match std::env::var("HOME") {
            Ok(h) => PathBuf::from(h).join(".local/state/dregg-telegram/sessions"),
            Err(_) => PathBuf::from("dregg-telegram-sessions"),
        });
    if let Err(e) = std::fs::create_dir_all(&session_dir) {
        eprintln!(
            "WARN: cannot create session dir {}: {e} — sessions will be in-memory",
            session_dir.display()
        );
    }

    // 4. The council electorate (derived member pubkeys from Telegram uids).
    let council_uids: Vec<u64> = std::env::var("TELEGRAM_COUNCIL_UIDS")
        .ok()
        .map(|s| {
            s.split(',')
                .filter_map(|t| t.trim().parse::<u64>().ok())
                .collect()
        })
        .unwrap_or_default();
    let members: Vec<[u8; 32]> = council_uids
        .iter()
        .map(|uid| TelegramHost::<LiveTransport>::council_member_pubkey(&bot_secret, *uid))
        .collect();

    // 5. The live edge: one shared reqwest client under both the send transport and the poller.
    let http = match ReqwestHttpPost::new() {
        Ok(h) => h,
        Err(e) => {
            eprintln!("cannot build the HTTP client: {e}");
            std::process::exit(1);
        }
    };
    let base = std::env::var("TELEGRAM_API_BASE")
        .ok()
        .filter(|b| !b.is_empty());
    let mut api = BotApi::new(token.clone(), http.clone());
    let mut transport = RawBotApi::new(token.clone(), http);
    if let Some(b) = &base {
        api = api.with_base_url(b.clone());
        transport = transport.with_base_url(b.clone());
    }

    // 6. Prove the token live BEFORE spinning anything (getMe): fail fast on a bad token.
    match api.get_me() {
        Ok(username) => eprintln!("dreggnet-telegram-bot: authenticated as @{username}"),
        Err(e) => {
            eprintln!("getMe failed ({e}) — is TELEGRAM_BOT_TOKEN valid? Exiting.");
            std::process::exit(2);
        }
    }

    // 7. The host: full shared catalog over the durable store, resumed on this boot — with the
    //    Mini App launch tier armed at the funnel base (env `TELEGRAM_WEBAPP_BASE`, defaulting
    //    to the hbox funnel): DMs get "🕹 Play in the app" web_app buttons + /play.
    let webapp_base = dreggnet_telegram::webapp::webapp_base_from_env();
    eprintln!("mini-app launch tier armed at {webapp_base} (TELEGRAM_WEBAPP_BASE overrides)");
    let dir_for_host = session_dir.clone();
    let mut host = TelegramHost::with_host(bot_secret, transport, move || {
        durable_telegram_host(Some(dir_for_host), members)
    })
    .with_webapp_base(webapp_base);

    // 8. The long-poll loop, with the consumed-updates offset persisted beside the sessions so a
    //    restart does not re-route already-answered presses.
    let offset_path = session_dir.join("updates.offset");
    let offset = std::fs::read_to_string(&offset_path)
        .ok()
        .and_then(|s| s.trim().parse::<i64>().ok());
    eprintln!(
        "long-polling getUpdates (sessions under {}; {} council member(s))",
        session_dir.display(),
        council_uids.len()
    );
    run_update_loop(&mut host, &api, offset, |n| {
        if let Err(e) = std::fs::write(&offset_path, n.to_string()) {
            eprintln!("WARN: cannot persist update offset: {e}");
        }
    });
}
