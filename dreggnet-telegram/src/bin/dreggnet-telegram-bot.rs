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
//! - with feature `private-bazaar-live`, the complete `DREGG_PRIVATE_BAZAAR_*`
//!   deployment record is optional; a partial/malformed record refuses startup.
//!
//! Deploy: `deploy/telegram/dregg-telegram-bot.service` + `deploy/telegram/RUNBOOK-TELEGRAM.md`.

use std::path::PathBuf;

use dreggnet_catalog::GameEpochLedger;
use dreggnet_telegram::host::TelegramHost;
use dreggnet_telegram::reqwest_transport::ReqwestHttpPost;
use dreggnet_telegram::runtime::{
    BotApi, durable_player_worlds, run_update_loop, try_durable_telegram_host,
};
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

    // 3b. The audit log — the interaction envelope (docs/BOT-AUDIT-LOGGING-DESIGN.md): a
    //     sibling `audit/` beside the session store unless `DREGG_AUDIT_DIR` overrides
    //     (`DREGG_AUDIT_DIR=off` disables). Armed BEFORE the host build so boot-resume
    //     decisions are the first recorded events.
    let audit_default = session_dir
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map(|p| p.join("audit"))
        .unwrap_or_else(|| std::path::PathBuf::from("audit"));
    let audit_log = dreggnet_telegram::audit::init(Some(audit_default));
    eprintln!(
        "audit log {} (DREGG_AUDIT_DIR overrides; off disables)",
        if audit_log.is_enabled() {
            "ENABLED"
        } else {
            "disabled"
        }
    );

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

    // 6a. REGISTER THE CLIENT-SIDE `/` MENU from the ONE command registry. Without this the
    //     Telegram client shows no command list (`getMyCommands` → `[]`) and the surface has to
    //     be guessed. Non-fatal: a bot that cannot register its menu still answers commands.
    match api.set_my_commands() {
        Ok(count) => eprintln!("registered {count} command(s) with Telegram's / menu"),
        Err(e) => eprintln!("WARN: setMyCommands failed ({e}) — the client / menu may be stale"),
    }

    // 6a-bis. ⚑ INSTALL THE VERIFIED DISTRIBUTED GATES — WITHOUT WHICH `/market` NEVER SETTLES.
    //     `/market` and the Dark Bazaar fold their award ring through
    //     `dregg_intent::verified_settle`, which the twin-deletion sweep made authoritative per
    //     leg: an unregistered `IntentVerifiedGate` REFUSES the leg, and a ring is all-or-none. So
    //     a player could list, bid, bid — three real committed turns — and then read "WIRING BUG in
    //     this host … the award was NEVER JUDGED" at the one turn that moves value. Nothing in this
    //     binary's graph registered one; `node/src/lib.rs`, `discord-bot/src/main.rs` and
    //     `dreggnet_web::install_verified_settlement_gate` all do this at startup.
    //     Non-fatal on purpose: the dungeon, the Descent and every non-settling offering play
    //     without it, and refusing to boot would take the whole bot down for one surface. The line
    //     below is how an operator learns which surface is dark.
    dregg_exec_lean::register_distributed_gates();
    if dregg_lean_ffi::distributed_exports_available() {
        eprintln!(
            "verified distributed gates installed (a market/Bazaar award is judged by the linked \
             verified executor)"
        );
    } else {
        eprintln!(
            "WARN: the linked archive exports no distributed coordination gates — /market and the \
             Dark Bazaar will REFUSE to settle an award (fail-closed, not degraded); every other \
             offering is unaffected"
        );
    }

    // 6b. ⚑ ARM THE DESCENT'S DAY BEFORE THE HOST IS BUILT — and keep it armed.
    //     The catalog registers the Descent against the LIVE verified drand day, so a run's
    //     banked relics mint under a provenance root that could not exist before that round was
    //     revealed. With no day published the open REFUSES (fail-closed); it never degrades to
    //     the pre-computable deploy-seed-derived root. Fetched + BLS-verified here and refreshed
    //     hourly on a background thread, which also carries the binding across the UTC day roll.
    match dreggnet_telegram::host::arm_todays_descent_day() {
        Ok(source) => {
            eprintln!("Descent day armed from {source} (banked-relic provenance is beacon-bound)")
        }
        Err(error) => eprintln!(
            "WARN: could not arm the Descent day ({error:?}) — the Descent will REFUSE to open \
             until a verified drand round is published (fail-closed, not degraded)"
        ),
    }
    std::thread::spawn(|| {
        loop {
            std::thread::sleep(std::time::Duration::from_secs(3600));
            if let Err(error) = dreggnet_telegram::host::arm_todays_descent_day() {
                eprintln!("WARN: Descent day refresh failed ({error:?}); opens fail closed");
            }
        }
    });

    // 7. The host: full shared catalog over the durable store, resumed on this boot — with the
    //    Mini App launch tier armed at the funnel base (env `TELEGRAM_WEBAPP_BASE`, defaulting
    //    to the hbox funnel): DMs get "🕹 Play in the app" web_app buttons + /play.
    let webapp_base = dreggnet_telegram::webapp::webapp_base_from_env();
    eprintln!("mini-app launch tier armed at {webapp_base} (TELEGRAM_WEBAPP_BASE overrides)");
    let dir_for_players = session_dir.clone();
    let game_epochs = match GameEpochLedger::open(session_dir.join("game-epochs")) {
        Ok(ledger) => ledger,
        Err(error) => {
            eprintln!("cannot open durable game epoch ledger: {error}. Exiting.");
            std::process::exit(2);
        }
    };
    let dir_for_host = session_dir.clone();
    #[cfg(feature = "private-bazaar-live")]
    let private_bazaar_deployment = match dreggnet_catalog::PrivateBazaarLiveDeployment::from_env()
    {
        Ok(deployment) => deployment,
        Err(error) => {
            eprintln!("private Bazaar deployment configuration refused: {error}. Exiting.");
            std::process::exit(2);
        }
    };

    #[cfg(feature = "private-bazaar-live")]
    let host_result = match private_bazaar_deployment {
        Some(deployment) => {
            let mounted = deployment.clone();
            eprintln!(
                "configured private Bazaar deployment mounted at {}",
                dreggnet_market::private_bazaar_live_host::PRIVATE_BAZAAR_RAID_KEY
            );
            TelegramHost::try_with_private_bazaar_hosts_and_game_epochs(
                bot_secret,
                transport,
                move || {
                    dreggnet_telegram::runtime::try_durable_telegram_host_with_private_bazaar(
                        dir_for_host,
                        members,
                        &mounted,
                    )
                },
                move || durable_player_worlds(Some(dir_for_players)),
                game_epochs,
                deployment,
            )
        }
        None => TelegramHost::try_with_hosts_and_game_epochs(
            bot_secret,
            transport,
            move || try_durable_telegram_host(dir_for_host, members),
            move || durable_player_worlds(Some(dir_for_players)),
            game_epochs,
        ),
    };
    #[cfg(not(feature = "private-bazaar-live"))]
    let host_result = TelegramHost::try_with_hosts_and_game_epochs(
        bot_secret,
        transport,
        move || try_durable_telegram_host(dir_for_host, members),
        // The per-identity RPG worlds, durable under the SAME session dir (one subdir per player)
        // — so trade / inventory / craft are isolated AND survive a restart, exactly like Discord.
        move || durable_player_worlds(Some(dir_for_players)),
        game_epochs,
    );
    let mut host = match host_result {
        Ok(host) => host.with_webapp_base(webapp_base),
        Err(error) => {
            eprintln!("cannot open durable Telegram host: {error}. Exiting.");
            std::process::exit(2);
        }
    };

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
