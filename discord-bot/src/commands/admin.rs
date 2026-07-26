//! `/dregg admin …` — the OPERATOR surface: the bot's own runtime settings and the honest
//! posture reads that used to exist only as boot-log lines.
//!
//! ## The gate
//!
//! Every subcommand here is refused for anyone not in [`crate::config::Config::admin_discord_ids`]
//! (`ADMIN_DISCORD_ID` ∪ `ADMIN_DISCORD_IDS`). The gate is **structural**, not per-handler: [`handle`]
//! resolves an [`AdminPlan`] BEFORE it looks at which subcommand was invoked, so a new subcommand
//! cannot be added on a path that skips the check. [`plan`] is pure and
//! [`AdminAction::ALL`] enumerates the whole surface, which is what lets a test assert the refusal
//! for EVERY action rather than for the ones someone remembered to cover.
//!
//! An unconfigured bot (no admin ids at all) refuses everyone — never "no admin configured, so
//! everyone is admin". Discord's own guild-administrator permission is deliberately NOT accepted
//! either: a guild admin has authority over their guild, not over this bot's narrator, treasury
//! and credit ledger, which are shared across every guild it serves.
//!
//! ## What is here, and why these four
//!
//! * **`narrator`** — the direct ask: change the AI narrator at runtime, persisted, without a
//!   redeploy. `chutes-tee` (Chutes/Bittensor inside a DCAP-verified TDX enclave) is the intended
//!   path; every other backend is offered as a labelled downgrade, and a switch that cannot be
//!   BUILT is refused with the reason rather than silently leaving something else running.
//! * **`status`** — the posture that is otherwise invisible. Above all **which payment watcher is
//!   live**: with no `DREGG_PAY_*` environment the bot builds a devnet config on a `MockWatcher`,
//!   and `/buy-credits` then hands out deposit addresses that NOTHING watches. That was a single
//!   boot-log line. It also names the node, the state producer, the federation id, the custody
//!   posture, and the narrator's price PROVENANCE.
//! * **`treasury`** — the refuel signal. `Treasury::spend_inference_usd` fails closed with
//!   `InsufficientFuel`, so an operator wants to know the tank is low BEFORE runs start failing;
//!   this reports how many runs the current fuel covers at the configured per-run ceiling.
//! * **`credits`** — inspect, and optionally grant, a user's run-credits. Granting is how the paid
//!   path gets exercised end-to-end without moving real money; it is a MINT, so it is admin-gated,
//!   `warn!`-logged with the actor, and recorded in the audit envelope.
//!
//! Nothing here can touch the pay path's watcher selection. `select_watcher` remains the only
//! thing that decides Mock vs Solana, it still refuses a mock on mainnet, and
//! [`crate::pay::PayState::watcher_kind`] is a read-only record of what it chose.

use serenity::all::{
    CommandDataOption, CommandDataOptionValue, CommandInteraction, CommandOptionType, Context,
    CreateCommand, CreateCommandOption, CreateEmbed, CreateInteractionResponse,
    CreateInteractionResponseMessage, EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;
use crate::pay::{
    BackendBuilders, NARRATOR_BACKENDS, NARRATOR_SETTING_KEY, NarratorSetting,
    load_narrator_setting, narrator_backend_is_attested, try_build_narrator,
};

/// One admin subcommand. Closed on purpose: [`Self::ALL`] is the whole surface, so a test can
/// drive the gate over EVERY action instead of over a hand-picked few, and adding a variant
/// without adding it to `ALL` is caught by [`Self::from_name`]'s round-trip test.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdminAction {
    /// Show, change, or reset the AI narrator.
    Narrator,
    /// The honest deployment posture (node, watcher, custody, narrator, federation).
    Status,
    /// The two-balance treasury + the refuel signal.
    Treasury,
    /// Inspect / grant a user's run-credits.
    Credits,
    /// WHO paid into the `$DREGG` pile, and what each stake is worth as a vote.
    Pool,
}

impl AdminAction {
    /// Every admin action — the enumeration the gate test walks.
    pub const ALL: &'static [AdminAction] = &[
        AdminAction::Narrator,
        AdminAction::Status,
        AdminAction::Treasury,
        AdminAction::Credits,
        AdminAction::Pool,
    ];

    /// The subcommand name as registered.
    pub const fn name(self) -> &'static str {
        match self {
            AdminAction::Narrator => "narrator",
            AdminAction::Status => "status",
            AdminAction::Treasury => "treasury",
            AdminAction::Credits => "credits",
            AdminAction::Pool => "pool",
        }
    }

    /// Parse a subcommand name. Total over [`Self::ALL`]; `None` otherwise.
    pub fn from_name(name: &str) -> Option<AdminAction> {
        AdminAction::ALL.iter().copied().find(|a| a.name() == name)
    }

    /// Whether this action MUTATES bot state (and therefore must be logged with its actor).
    pub const fn mutates(self) -> bool {
        matches!(self, AdminAction::Narrator | AdminAction::Credits)
    }
}

/// What [`handle`] will do — resolved BEFORE the subcommand is read, so the gate cannot be
/// bypassed by a subcommand that forgets to check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdminPlan {
    /// The caller is not an admin (or the bot has no admins configured): refuse.
    Refused,
    /// The caller is an admin and named a known action: run it.
    Run(AdminAction),
    /// The caller is an admin but named nothing recognisable: show the admin menu.
    Menu,
}

/// **The gate, as a pure function.** `is_admin` is the ONLY thing that admits; the subcommand
/// name only chooses *which* admitted action runs. A non-admin gets [`AdminPlan::Refused`] for
/// every input, including inputs this build does not recognise.
pub fn plan(is_admin: bool, sub: Option<&str>) -> AdminPlan {
    if !is_admin {
        return AdminPlan::Refused;
    }
    match sub.and_then(AdminAction::from_name) {
        Some(action) => AdminPlan::Run(action),
        None => AdminPlan::Menu,
    }
}

/// The refusal a non-admin sees. Deliberately says only that the action is operator-only — it
/// does not enumerate the admins, and it does not hint at what the actions do.
pub fn refusal_embed() -> CreateEmbed {
    embeds::warning_embed(
        "Admin only",
        "`/dregg admin` drives this bot's own operator settings — the AI narrator it pays for, \
         its treasury, and its run-credit ledger — which are shared across every server it \
         serves. Only the operator can change them.",
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration
// ─────────────────────────────────────────────────────────────────────────────

/// Register the `admin` surface. Folded into `/dregg` as a subcommand GROUP by
/// `commands::menus::dregg_command` — NOT a 14th top-level command; the global slash surface
/// stays exactly 13 (`crate::REGISTERED_COMMAND_NAMES`).
pub fn register() -> CreateCommand {
    let mut backend = CreateCommandOption::new(
        CommandOptionType::String,
        "backend",
        "Which narrator backend (chutes-tee is the attested, intended path)",
    );
    for (key, description) in NARRATOR_BACKENDS {
        // Discord caps a choice name at 100 chars; the keys + descriptions here are well under.
        backend = backend.add_string_choice(format!("{key} — {description}"), *key);
    }

    CreateCommand::new("admin")
        .description("Operator-only: the narrator, the deployment posture, the treasury, credits")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "narrator",
                "Show or change the AI narrator (persisted; chutes-tee is the attested path)",
            )
            .add_sub_option(backend)
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::String,
                "model",
                "The model id (on chutes-tee this must be a -TEE chute)",
            ))
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::Number,
                "price_in_per_1k",
                "USD per 1,000 INPUT tokens for that model (both prices or neither)",
            ))
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::Number,
                "price_out_per_1k",
                "USD per 1,000 OUTPUT tokens for that model (both prices or neither)",
            ))
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::Boolean,
                "reset",
                "Drop the stored setting and go back to the environment default",
            )),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "The honest posture: node, payment watcher, custody, narrator, federation",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "treasury",
            "Fuel (USDC) + pile ($DREGG), and how many runs the fuel still covers",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "pool",
            "Who paid into the $DREGG pile, and each stake's quadratic vote weight",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "credits",
                "Inspect (and optionally grant) a user's run-credits",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::User, "user", "Whose credits")
                    .required(true),
            )
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::Integer,
                "grant",
                "Mint this many run-credits to them (operator-funded; logged)",
            )),
        )
}

// ─────────────────────────────────────────────────────────────────────────────
// Dispatch
// ─────────────────────────────────────────────────────────────────────────────

/// Handle `/dregg admin …`.
///
/// The ordering is the gate: `plan` is consulted with the caller's admin status FIRST, and a
/// refusal returns before any action is selected or any state is read.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let sub = invoked_sub(command);
    let decision = plan(state.config.is_admin(user_id), sub.as_deref());

    if decision == AdminPlan::Refused {
        tracing::warn!(
            user_id,
            requested = sub.as_deref().unwrap_or("(menu)"),
            "REFUSED a non-admin /dregg admin invocation"
        );
        crate::audit::log().emit(
            crate::audit::AuditEvent::new(
                "discord",
                crate::audit::custodial_actor(state, user_id),
                crate::audit::Surface::Command,
                crate::audit::Input {
                    kind: "admin".to_string(),
                    detail: serde_json::json!({
                        "sub": sub.as_deref().unwrap_or(""),
                    }),
                },
            )
            .decided("refused", "not_admin"),
        );
        respond(ctx, command, refusal_embed()).await;
        return;
    }

    let AdminPlan::Run(action) = decision else {
        respond(ctx, command, menu_embed(state)).await;
        return;
    };

    if action.mutates() {
        tracing::info!(
            user_id,
            action = action.name(),
            "admin action authorized (a MUTATING one)"
        );
    }

    // Defer: the status read hits the node and a narrator rebuild can do TEE discovery +
    // attestation, both well past Discord's 3-second window.
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;

    let embed = match action {
        AdminAction::Narrator => run_narrator(command, state, user_id).await,
        AdminAction::Status => run_status(state).await,
        AdminAction::Treasury => run_treasury(state),
        AdminAction::Credits => run_credits(command, state, user_id).await,
        AdminAction::Pool => run_pool(state).await,
    };

    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// The invoked subcommand name under the `admin` group, if any.
fn invoked_sub(command: &CommandInteraction) -> Option<String> {
    command.data.options.first().map(|o| o.name.clone())
}

/// The options nested inside the invoked subcommand.
fn sub_options(command: &CommandInteraction) -> Vec<CommandDataOption> {
    match command.data.options.first().map(|o| &o.value) {
        Some(CommandDataOptionValue::SubCommand(v)) => v.clone(),
        _ => Vec::new(),
    }
}

fn opt_string(opts: &[CommandDataOption], name: &str) -> Option<String> {
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.trim().to_string()),
            _ => None,
        })
        .filter(|s| !s.is_empty())
}

fn opt_number(opts: &[CommandDataOption], name: &str) -> Option<f64> {
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Number(n) => Some(*n),
            _ => None,
        })
}

fn opt_integer(opts: &[CommandDataOption], name: &str) -> Option<i64> {
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(i) => Some(*i),
            _ => None,
        })
}

fn opt_bool(opts: &[CommandDataOption], name: &str) -> Option<bool> {
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Boolean(b) => Some(*b),
            _ => None,
        })
}

fn opt_user(opts: &[CommandDataOption], name: &str) -> Option<u64> {
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::User(uid) => Some(uid.get()),
            _ => None,
        })
}

async fn respond(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

fn menu_embed(state: &BotState) -> CreateEmbed {
    let status = state.pay.narrator_status();
    embeds::dregg_embed("Operator controls")
        .description(format!(
            "Narrator right now: **{}**{}.\n\n\
             • `/dregg admin narrator` — show / change / reset the AI narrator (persisted)\n\
             • `/dregg admin status` — node, payment watcher, custody, narrator, federation\n\
             • `/dregg admin treasury` — fuel + pile, and the refuel signal\n\
             • `/dregg admin credits user:<@u> [grant:<n>]` — inspect or mint run-credits\n\
             • `/dregg admin pool` — who paid into the $DREGG pile + their vote weights",
            status.backend_key,
            if status.attested {
                " (attested enclave)"
            } else {
                ""
            },
        ))
        .field(
            "The pay path is not reachable from here",
            "No admin action can change which payment watcher runs. `select_watcher` decides \
             that once, at construction, from the operator environment — and it refuses a mock \
             on mainnet outright.",
            false,
        )
}

// ─────────────────────────────────────────────────────────────────────────────
// `/dregg admin narrator`
// ─────────────────────────────────────────────────────────────────────────────

/// Render the narrator surface, and — when options were supplied — apply the change.
///
/// The change is **build-then-commit**: the replacement narrator is constructed (which validates
/// the backend's configuration AND that the model is priced) before anything is persisted or
/// swapped in. A build failure changes nothing at all and reports the reason, so a fat-fingered
/// switch can never take the bot off the attested backend.
async fn run_narrator(command: &CommandInteraction, state: &BotState, actor: u64) -> CreateEmbed {
    let opts = sub_options(command);
    let reset = opt_bool(&opts, "reset").unwrap_or(false);
    let backend = opt_string(&opts, "backend");
    let model = opt_string(&opts, "model");
    let price_in = opt_number(&opts, "price_in_per_1k");
    let price_out = opt_number(&opts, "price_out_per_1k");

    let stored = match load_narrator_setting(&state.db).await {
        Ok(s) => s,
        Err(reason) => {
            tracing::error!(%reason, "stored narrator setting is unreadable");
            None
        }
    };

    // ── READ (no options supplied) ───────────────────────────────────────────
    if !reset && backend.is_none() && model.is_none() && price_in.is_none() && price_out.is_none() {
        return narrator_report(state, stored.as_ref(), None);
    }

    // ── RESET ────────────────────────────────────────────────────────────────
    if reset {
        // Rebuild from the environment alone; only then drop the stored row, so a reset that
        // cannot produce a working narrator is still honest about what is now running.
        let built =
            tokio::task::spawn_blocking(|| try_build_narrator(None, &BackendBuilders::from_env()))
                .await
                .unwrap_or_else(|e| Err(format!("narrator rebuild panicked: {e}")));
        let cleared = state.db.clear_setting(NARRATOR_SETTING_KEY).await;
        match built {
            Ok(narrator) => {
                let now = describe_built(&narrator);
                state.pay.set_paid(narrator);
                tracing::warn!(
                    actor,
                    cleared = cleared.unwrap_or(false),
                    now = %now,
                    "admin RESET the narrator to the environment default"
                );
                narrator_report(
                    state,
                    None,
                    Some(Ok(format!(
                        "Reset to the environment default (`DREGG_NARRATOR`). Now running: **{now}**."
                    ))),
                )
            }
            Err(reason) => {
                state.pay.set_paid(None);
                tracing::error!(actor, %reason, "admin reset left NO narrator");
                narrator_report(
                    state,
                    None,
                    Some(Err(format!(
                        "The stored setting was cleared, but the environment default could not be \
                     built: {reason}\n\nPaid runs use the FREE TIER until this is fixed — nothing \
                     was substituted."
                    ))),
                )
            }
        }
    } else {
        // ── CHANGE ───────────────────────────────────────────────────────────
        // Start from the stored setting so a partial change (just the model, say) keeps the rest.
        let mut next = stored.clone().unwrap_or_default();
        if let Some(b) = backend.clone() {
            next.backend = Some(b);
        }
        if let Some(m) = model.clone() {
            next.model = Some(m);
        }
        if price_in.is_some() {
            next.price_input_per_1k = price_in;
        }
        if price_out.is_some() {
            next.price_output_per_1k = price_out;
        }
        next.set_by = Some(actor);
        next.set_at = now_secs();

        // Half a price pins nothing (`ModelRegistry::apply_price_override`), so refuse it here
        // with a legible reason rather than letting it surface as `UnpricedModel` at build.
        if next.price_input_per_1k.is_some() != next.price_output_per_1k.is_some() {
            return narrator_report(
                state,
                stored.as_ref(),
                Some(Err(
                    "Give BOTH `price_in_per_1k` and `price_out_per_1k`, or neither. \
                          Half a price pins nothing — the model would stay unpriced and every \
                          call would be refused."
                        .to_string(),
                )),
            );
        }

        let candidate = next.clone();
        let built = tokio::task::spawn_blocking(move || {
            try_build_narrator(Some(&candidate), &BackendBuilders::from_env())
        })
        .await
        .unwrap_or_else(|e| Err(format!("narrator build panicked: {e}")));

        match built {
            Ok(narrator) => {
                let now = describe_built(&narrator);
                // COMMIT: swap first (so the change is live even if the write fails), then persist.
                state.pay.set_paid(narrator);
                let persisted = state
                    .db
                    .set_setting(NARRATOR_SETTING_KEY, &next.to_json())
                    .await;
                tracing::warn!(
                    actor,
                    backend = next.backend.as_deref().unwrap_or("(env)"),
                    model = next.model.as_deref().unwrap_or("(env)"),
                    now = %now,
                    "admin CHANGED the narrator"
                );
                let note = match persisted {
                    Ok(()) => {
                        format!("Narrator is now **{now}**. Persisted — it survives restart.")
                    }
                    Err(e) => format!(
                        "Narrator is now **{now}**, but the setting could NOT be persisted \
                         ({e}) — it will revert to the environment default on restart."
                    ),
                };
                narrator_report(state, Some(&next), Some(Ok(note)))
            }
            Err(reason) => {
                // REFUSED — nothing swapped, nothing written. Whatever was running still is.
                tracing::warn!(actor, %reason, "admin narrator change REFUSED");
                narrator_report(
                    state,
                    stored.as_ref(),
                    Some(Err(format!(
                        "Refused — **nothing changed**. {reason}\n\nThe narrator that was running \
                         before this command is still running."
                    ))),
                )
            }
        }
    }
}

/// A one-line description of a freshly-built narrator.
fn describe_built(narrator: &Option<crate::pay::PaidNarrator>) -> String {
    match narrator {
        Some(n) => format!("{}:{}", n.provider().backend_key(), n.model()),
        None => "none (free tier only)".to_string(),
    }
}

/// The narrator surface: what is live, what is stored, what is on offer, and the outcome of a
/// change when one was attempted.
fn narrator_report(
    state: &BotState,
    stored: Option<&NarratorSetting>,
    outcome: Option<Result<String, String>>,
) -> CreateEmbed {
    let status = state.pay.narrator_status();

    let live = match (&status.model, status.usd_per_run) {
        (Some(model), Some(usd)) => format!(
            "**{}** · model `{model}` · ceiling **${usd:.4}/run**{}",
            status.backend_key,
            if status.attested {
                " · **ATTESTED** (DCAP-verified TDX enclave)"
            } else {
                " · unattested"
            },
        ),
        _ => "**none** — every run uses the free tier (local ollama, else scripted prose)"
            .to_string(),
    };

    let price = match status.price {
        Some((input, output, source)) => format!(
            "`${input}`/1k in · `${output}`/1k out · provenance **{source}**{}",
            if source == "operator-override" {
                "\n⚠ An operator-set rate is trusted at your discretion and is NOT guaranteed to \
                 be an upper bound. Set below the provider's true cost and the per-run ceiling \
                 LEAKS — the ledger meters the real token counts against a rate that understates \
                 them."
            } else {
                ""
            }
        ),
        None => "**UNPRICED** — the metered layer refuses every call, so this narrator produces \
                 nothing. Pin both rates."
            .to_string(),
    };

    let stored_line = match stored {
        None => "_none — following the environment (`DREGG_NARRATOR`)_".to_string(),
        Some(s) => format!(
            "backend `{}` · model `{}`{}{}",
            s.backend.as_deref().unwrap_or("(env)"),
            s.model.as_deref().unwrap_or("(env)"),
            match (s.price_input_per_1k, s.price_output_per_1k) {
                (Some(i), Some(o)) => format!(" · price `{i}`/`{o}` per 1k"),
                _ => String::new(),
            },
            match s.set_by {
                Some(who) => format!(" · set by <@{who}>"),
                None => String::new(),
            },
        ),
    };

    let offered = NARRATOR_BACKENDS
        .iter()
        .map(|(key, description)| {
            format!(
                "{} `{key}` — {description}",
                if narrator_backend_is_attested(key) {
                    "🔒"
                } else {
                    "•"
                }
            )
        })
        .collect::<Vec<_>>()
        .join("\n");

    let mut embed = match &outcome {
        Some(Ok(_)) => embeds::success_embed("Narrator"),
        Some(Err(_)) => embeds::warning_embed("Narrator", ""),
        None => embeds::dregg_embed("Narrator"),
    };
    if let Some(result) = outcome {
        let text = match result {
            Ok(t) => t,
            Err(t) => t,
        };
        embed = embed.description(text);
    } else {
        embed = embed.description(
            "`chutes-tee` is the intended path: the same Chutes/Bittensor inference, run inside a \
             DCAP-verified Intel TDX enclave. The request is ML-KEM-768-encapsulated to a key \
             bound into a quote this bot verified against a pinned measurement registry. What \
             that establishes is WHERE the text was produced and the code identity of the serving \
             enclave — never a claim about the weights or the sampled tokens.",
        );
    }

    embed
        .field("Live now", live, false)
        .field("Price", price, false)
        .field("Stored setting", stored_line, false)
        .field("Backends", offered, false)
        .field(
            "Changing it",
            "`/dregg admin narrator backend:<key> model:<id> price_in_per_1k:<n> \
             price_out_per_1k:<n>` — the change is built and priced BEFORE it is committed, so a \
             switch that cannot work is refused and nothing changes. \
             `reset:true` drops the stored setting and returns to the environment.",
            false,
        )
}

// ─────────────────────────────────────────────────────────────────────────────
// `/dregg admin status`
// ─────────────────────────────────────────────────────────────────────────────

#[derive(serde::Deserialize, Default)]
struct NodeStatus {
    #[serde(default)]
    healthy: bool,
    #[serde(default)]
    federation_mode: String,
    #[serde(default)]
    state_producer: String,
    #[serde(default)]
    lean_producer: bool,
    #[serde(default)]
    consensus_live: bool,
    #[serde(default)]
    latest_height: u64,
}

/// The honest deployment posture.
async fn run_status(state: &BotState) -> CreateEmbed {
    let pay = &state.pay;

    // ── the node ─────────────────────────────────────────────────────────────
    let url = state.config.devnet_url.trim_end_matches('/').to_string();
    let node = match state
        .devnet
        .client()
        .get(format!("{url}/status"))
        .send()
        .await
    {
        Ok(r) if r.status().is_success() => r.json::<NodeStatus>().await.ok(),
        _ => None,
    };
    let node_line = match &node {
        Some(s) => format!(
            "`{url}` — {} · consensus {} · height {}",
            if s.healthy { "healthy" } else { "degraded" },
            if s.consensus_live { "live" } else { "idle" },
            s.latest_height,
        ),
        None => format!("`{url}` — **UNREACHABLE** (every node-backed command will fail)"),
    };
    let producer = match &node {
        Some(s) if !s.state_producer.is_empty() => format!(
            "{}{}",
            s.state_producer,
            if s.lean_producer {
                " (Lean-authored)"
            } else {
                " (rust)"
            }
        ),
        Some(s) if s.lean_producer => "lean".to_string(),
        Some(_) => "rust".to_string(),
        None => "unknown (node unreachable)".to_string(),
    };

    // ── the money ────────────────────────────────────────────────────────────
    let watching_real = pay.watcher_kind == crate::pay::REAL_WATCHER_KIND;
    let watcher_line = format!(
        "**{}** on **{:?}**\n{}",
        pay.watcher_kind,
        pay.network(),
        if watching_real {
            "Deposit addresses issued by `/buy-credits` ARE being polled."
        } else {
            "⚠ **NOTHING IS WATCHING.** `/buy-credits` still issues deposit addresses, but a mock \
             watcher observes no chain — a real payment to one of those addresses would never be \
             credited. This is the correct state for local dev and a real hazard anywhere else."
        }
    );
    let custody = if pay.deposits.is_watch_only() {
        "watch-only — this process holds NO signing seed"
    } else {
        "custodial/devnet — this process holds a seed (correct only for the throwaway devnet \
         fallback or a deliberately-custodial operator)"
    };

    // ── the narrator ─────────────────────────────────────────────────────────
    let n = pay.narrator_status();
    let narrator_line = match &n.model {
        Some(model) => format!(
            "**{}** · `{model}`{}\nprice provenance: **{}**",
            n.backend_key,
            if n.attested {
                " · ATTESTED enclave"
            } else {
                " · unattested"
            },
            n.price
                .map(|(_, _, s)| s)
                .unwrap_or("UNPRICED — refuses every call"),
        ),
        None => "**none** — every run falls to the free tier".to_string(),
    };

    embeds::dregg_embed("Operator posture")
        .description(
            "What this process is ACTUALLY doing — the facts that otherwise live only in the boot \
             log.",
        )
        .field("Node", node_line, false)
        .field("State producer", producer, true)
        .field(
            "Federation id",
            format!("`{}`", hex::encode(state.federation_id_bytes)),
            false,
        )
        .field("Payment watcher", watcher_line, false)
        .field("Custody", custody, false)
        .field(
            "Price per run",
            format!("{} atomic $DREGG", pay.price_per_run()),
            true,
        )
        .field("Narrator", narrator_line, false)
        .field(
            "Admins",
            format!(
                "{} configured (`ADMIN_DISCORD_ID` ∪ `ADMIN_DISCORD_IDS`)",
                state.config.admin_discord_ids.len()
            ),
            true,
        )
}

// ─────────────────────────────────────────────────────────────────────────────
// `/dregg admin treasury`
// ─────────────────────────────────────────────────────────────────────────────

/// The treasury + the refuel signal.
fn run_treasury(state: &BotState) -> CreateEmbed {
    let pay = &state.pay;
    let fuel = pay.treasury_fuel();
    let pile = pay.treasury_pile();
    let usd_per_run = pay.narrator_status().usd_per_run;

    // The fuel tank is atomic USDC; `usdc_decimals` on the config gives the scale.
    let decimals = pay.config.usdc_decimals as u32;
    let scale = 10u64.pow(decimals.min(18)) as f64;
    let fuel_usd = fuel as f64 / scale;

    let refuel = match usd_per_run {
        Some(usd) if usd > 0.0 => {
            let runs = (fuel_usd / usd).floor() as u64;
            if runs == 0 {
                format!(
                    "🔴 **REFUEL NOW.** ${fuel_usd:.4} of fuel does not cover even one run at the \
                     ${usd:.4} per-run ceiling. `spend_inference_usd` fails closed with \
                     `InsufficientFuel`, so real-AI runs will start refusing."
                )
            } else if runs < 20 {
                format!("🟡 ${fuel_usd:.4} of fuel ≈ **{runs}** run(s) at ${usd:.4}/run — low.")
            } else {
                format!("🟢 ${fuel_usd:.4} of fuel ≈ **{runs}** run(s) at ${usd:.4}/run.")
            }
        }
        _ => format!(
            "${fuel_usd:.4} of fuel. No narrator is active, so nothing is currently burning it."
        ),
    };

    embeds::dregg_embed("Treasury")
        .description(format!(
            "Where detected game revenue lands. A USDC payment fuels the tank (burned per \
             real-AI run, fail-closed on empty); a $DREGG payment grows the illiquid pile. Every \
             run burns USD fuel regardless of how the player paid.\n\n{refuel}"
        ))
        .field("Fuel (USDC atomic)", format!("`{fuel}`"), true)
        .field("Pile ($DREGG atomic)", format!("`{pile}`"), true)
        .field(
            "Declared cross-chain positions",
            {
                let slots = pay.treasury_slots();
                if slots.is_empty() {
                    "_none declared_".to_string()
                } else {
                    slots
                        .iter()
                        .map(|s| format!("• {}", s.label))
                        .collect::<Vec<_>>()
                        .join("\n")
                }
            },
            false,
        )
}

// ─────────────────────────────────────────────────────────────────────────────
// `/dregg admin credits`
// ─────────────────────────────────────────────────────────────────────────────

/// Inspect, and optionally grant, a user's run-credits.
///
/// A grant is a MINT of operator-funded value (the operator pays the inference these credits
/// buy). It is therefore admin-gated, warn-logged with the acting admin, and recorded in the
/// audit envelope — and the embed says plainly that it was minted, not paid for.
async fn run_credits(command: &CommandInteraction, state: &BotState, actor: u64) -> CreateEmbed {
    let opts = sub_options(command);
    let Some(target) = opt_user(&opts, "user") else {
        return embeds::error_embed("Missing user", "Name the user whose credits to inspect.");
    };
    let discord_id = target.to_string();
    let grant = opt_integer(&opts, "grant").unwrap_or(0);

    let before = state.pay.balance_checked(&discord_id).await;
    let mut note = String::new();

    if grant > 0 {
        let grant = grant as u64;
        let base = before.as_ref().copied().unwrap_or_else(|_| 0);
        if before.is_err() {
            return embeds::error_embed(
                "Ledger unreadable",
                "The credit ledger could not be read, so a grant would be computed from an \
                 unknown balance. Refusing — retry when storage recovers.",
            );
        }
        let next = base.saturating_add(grant);
        match state.db.pay_set_credit_balance(&discord_id, next).await {
            Ok(()) => {
                tracing::warn!(
                    actor,
                    target,
                    grant,
                    before = base,
                    after = next,
                    "admin MINTED run-credits"
                );
                crate::audit::log().emit(
                    crate::audit::AuditEvent::new(
                        "discord",
                        crate::audit::custodial_actor(state, actor),
                        crate::audit::Surface::Command,
                        crate::audit::Input {
                            kind: "admin.credits.grant".to_string(),
                            detail: serde_json::json!({
                                "target": discord_id,
                                "grant": grant,
                                "before": base,
                                "after": next,
                            }),
                        },
                    )
                    .decided("granted", ""),
                );
                note = format!(
                    "\n\n**Minted {grant} run-credit(s)** to <@{target}> (was {base}, now {next}). \
                     These were NOT paid for — the operator funds the inference they buy. \
                     Recorded in the audit log against <@{actor}>."
                );
            }
            Err(e) => {
                return embeds::error_embed(
                    "Grant failed",
                    &format!("The ledger write failed ({e}); nothing was granted."),
                );
            }
        }
    } else if grant < 0 {
        note = "\n\n_A negative `grant` is ignored — this surface only mints._".to_string();
    }

    let balance = state.pay.balance_checked(&discord_id).await;
    let shown = match &balance {
        Ok(b) => format!("**{b}** run-credit(s)"),
        Err(_) => "**unavailable** (a storage failure — this is NOT a zero)".to_string(),
    };

    let deposit = state
        .pay
        .deposit_address_checked(&discord_id)
        .map(|a| format!("`{}`", a.to_base58()))
        .unwrap_or_else(|e| format!("_not provisioned_ ({e})"));

    embeds::dregg_embed("Run-credits")
        .description(format!("<@{target}> holds {shown}.{note}"))
        .field("Deposit address", deposit, false)
        .field(
            "Price per run",
            format!("{} atomic $DREGG", state.pay.price_per_run()),
            true,
        )
}

// ─────────────────────────────────────────────────────────────────────────────
// `/dregg admin pool` — WHO paid into the pile, and what that stake votes with.
// ─────────────────────────────────────────────────────────────────────────────

/// How close two contributions have to be, in size and in time, before they are flagged as a
/// possible split stake. Deliberately crude: this is a "look at these" prompt for a human, not a
/// verdict, and it has no consequence attached.
const SPLIT_WINDOW_SECS: i64 = 60 * 60 * 6;
/// Two stakes within this fraction of each other count as "near-equal".
const SPLIT_SIZE_TOLERANCE: f64 = 0.15;

/// The `$DREGG` pile's per-contributor attribution + quadratic vote weights.
///
/// **Why this view exists.** The swap vote weighs a contributor at `isqrt(atomic $DREGG)`.
/// Quadratic weight is sybil-**favourable** — `√a + √b > √(a+b)` — so splitting one stake across
/// two deposit addresses GAINS voting weight. That was decided knowingly, with a stated defence
/// that is social: someone notices and deals with it. Nothing surfaced the per-contributor
/// attribution, so nobody could notice. This is the view that makes the stated plan executable.
///
/// **Read-only, on purpose.** There is no exclude/ban affordance here. Excluding a contributor
/// from a pool they paid real `$DREGG` into is a decision with real consequences and it has not
/// been asked for; surfacing the data is the ask, and the action stays with a human.
async fn run_pool(state: &BotState) -> CreateEmbed {
    let rows = match state.db.pool_contributions().await {
        Ok(rows) => rows,
        Err(e) => {
            return embeds::error_embed(
                "Pool unreadable",
                &format!("The contribution ledger could not be read ({e})."),
            );
        }
    };

    if rows.is_empty() {
        return embeds::dregg_embed("$DREGG pool — contributors").description(
            "No `$DREGG` contributions attributed yet.\n\nAttribution is written when a \
                 `$DREGG` payment is newly credited by the payment poll, so an empty view means \
                 either nobody has paid in, or nothing is being watched — check \
                 `/dregg admin status` for which payment watcher is live.",
        );
    }

    // The same weight function the vote uses — derived, never stored, so an operator view and a
    // ballot cannot disagree about what a stake is worth.
    let weighted: Vec<(&crate::db::PoolContribution, u64)> = rows
        .iter()
        .map(|r| (r, dregg_pay::quadratic_weight(r.contributed)))
        .collect();

    let pool_total: u64 = rows
        .iter()
        .fold(0u64, |a, r| a.saturating_add(r.contributed));
    // Checked, matching `PoolSnapshot::total_weight`: a wrapped denominator would understate the
    // electorate and make any quorum look reachable.
    let total_weight: Option<u64> = weighted
        .iter()
        .try_fold(0u64, |acc, (_, w)| acc.checked_add(*w));

    // Already sorted by contribution DESC in SQL, which is also weight order (isqrt is monotone).
    let mut lines = Vec::new();
    for (row, weight) in weighted.iter().take(20) {
        let share = match total_weight {
            Some(t) if t > 0 => format!("{:.1}%", (*weight as f64 / t as f64) * 100.0),
            _ => "—".to_string(),
        };
        let addr = &row.deposit_address;
        let short: String = addr.chars().take(8).collect();
        lines.push(format!(
            "`{short}…` <@{}> · **{}** atomic · weight **{weight}** ({share}) · {} payment(s) · first <t:{}:R>",
            row.user, row.contributed, row.payments, row.first_seen
        ));
    }
    if weighted.len() > 20 {
        lines.push(format!("_…and {} more_", weighted.len() - 20));
    }

    let clusters = split_stake_clusters(&weighted);
    let cluster_note = if clusters.is_empty() {
        "No near-equal, near-simultaneous stake clusters stand out. That is not a proof of \
         absence — it is one crude heuristic over one table."
            .to_string()
    } else {
        format!(
            "⚠ **{} cluster(s) worth a look.** Each is a set of stakes within {:.0}% of each \
             other in size that first appeared within {} hours of one another — the shape a \
             split stake makes. This is a prompt for a human, not a verdict, and nothing here \
             acts on it.\n{}",
            clusters.len(),
            SPLIT_SIZE_TOLERANCE * 100.0,
            SPLIT_WINDOW_SECS / 3600,
            clusters
                .iter()
                .map(|c| format!(
                    "• {} stakes ≈ {} atomic each, combined weight **{}** vs **{}** if they were \
                     one stake",
                    c.count, c.each, c.split_weight, c.merged_weight
                ))
                .collect::<Vec<_>>()
                .join("\n"),
        )
    };

    embeds::dregg_embed("$DREGG pool — contributors")
        .description(format!(
            "Who paid into the pile, and what each stake is worth as a vote. Weight is \
             `isqrt(atomic $DREGG)` — the exact same `dregg_pay::quadratic_weight` a swap ballot \
             uses.\n\n{cluster_note}"
        ))
        .field("Contributors (heaviest first)", lines.join("\n"), false)
        .field("Pool total", format!("`{pool_total}` atomic $DREGG"), true)
        .field(
            "Total weight (the quorum denominator)",
            match total_weight {
                Some(t) => format!("**{t}** over {} contributor(s)", weighted.len()),
                None => "**overflowed** — refused rather than wrapped".to_string(),
            },
            true,
        )
        .field(
            "What this is and is not",
            "Quadratic weight is sybil-FAVOURABLE: `√a + √b > √(a+b)`, so splitting a stake \
             across two deposit addresses gains voting weight. That is a known, deliberate \
             choice; the defence is social, and this view is what makes noticing possible. \
             \n\nIt is the attribution THIS bot observed and credited — a payment credited by \
             another process is not here. It is read-only: no exclusion, no ban.",
            false,
        )
}

/// A set of near-equal, near-simultaneous stakes — the shape a split stake makes.
#[derive(Debug, PartialEq, Eq)]
struct SplitCluster {
    /// How many stakes are in the cluster.
    count: usize,
    /// Their representative (largest) size, in atomic `$DREGG`.
    each: u64,
    /// Their combined quadratic weight AS SPLIT — what the pool actually counts.
    split_weight: u64,
    /// The weight the same total would have carried as ONE stake. The gap between this and
    /// `split_weight` is exactly what splitting bought.
    merged_weight: u64,
}

/// Group contributions into near-equal, near-simultaneous clusters.
///
/// Deliberately crude and deliberately consequence-free: it is a highlighter over a table a human
/// is already looking at. It cannot prove a split (two people can legitimately pay similar amounts
/// at the same time) and it cannot rule one out (a patient adversary spreads their payments out).
/// Pure, so its behaviour is testable without a database.
fn split_stake_clusters(weighted: &[(&crate::db::PoolContribution, u64)]) -> Vec<SplitCluster> {
    let mut clusters = Vec::new();
    let mut used = vec![false; weighted.len()];
    for i in 0..weighted.len() {
        if used[i] {
            continue;
        }
        let (base, _) = weighted[i];
        if base.contributed == 0 {
            continue;
        }
        let mut group = vec![i];
        for j in (i + 1)..weighted.len() {
            if used[j] {
                continue;
            }
            let (other, _) = weighted[j];
            let size_gap = (base.contributed as f64 - other.contributed as f64).abs()
                / base.contributed as f64;
            let time_gap = (base.first_seen - other.first_seen).abs();
            if size_gap <= SPLIT_SIZE_TOLERANCE && time_gap <= SPLIT_WINDOW_SECS {
                group.push(j);
            }
        }
        if group.len() < 2 {
            continue;
        }
        for &k in &group {
            used[k] = true;
        }
        let total: u64 = group
            .iter()
            .fold(0u64, |a, &k| a.saturating_add(weighted[k].0.contributed));
        let split_weight: u64 = group
            .iter()
            .fold(0u64, |a, &k| a.saturating_add(weighted[k].1));
        clusters.push(SplitCluster {
            count: group.len(),
            each: base.contributed,
            split_weight,
            merged_weight: dregg_pay::quadratic_weight(total),
        });
    }
    clusters
}

fn now_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **THE GATE, over the WHOLE surface.** A non-admin is refused for every registered admin
    /// action AND for the bare menu AND for an unrecognised subcommand — the enumeration is
    /// [`AdminAction::ALL`], so an action added later is covered without anyone remembering to
    /// extend this test.
    #[test]
    fn a_non_admin_is_refused_for_every_admin_action() {
        for action in AdminAction::ALL {
            assert_eq!(
                plan(false, Some(action.name())),
                AdminPlan::Refused,
                "`/dregg admin {}` must be refused for a non-admin",
                action.name()
            );
        }
        assert_eq!(plan(false, None), AdminPlan::Refused, "the bare menu too");
        assert_eq!(
            plan(false, Some("something-new")),
            AdminPlan::Refused,
            "an unrecognised subcommand is refused, not menu'd"
        );
    }

    /// The complement — the gate is not vacuous: an admin reaches every action.
    #[test]
    fn an_admin_reaches_every_admin_action() {
        for action in AdminAction::ALL {
            assert_eq!(
                plan(true, Some(action.name())),
                AdminPlan::Run(*action),
                "an admin must reach `/dregg admin {}`",
                action.name()
            );
        }
        assert_eq!(plan(true, None), AdminPlan::Menu);
        assert_eq!(plan(true, Some("nope")), AdminPlan::Menu);
    }

    /// Every REGISTERED subcommand is a known [`AdminAction`] — so no subcommand can exist on the
    /// Discord surface that `plan` would route to the (unauthenticated-looking) menu arm instead
    /// of an admin-gated action. The registry is the source of truth, walked structurally.
    #[test]
    fn every_registered_subcommand_is_a_gated_action() {
        let json = serde_json::to_value(register()).expect("the command serializes");
        let subs: Vec<String> = json["options"]
            .as_array()
            .expect("admin has subcommands")
            .iter()
            .map(|o| o["name"].as_str().expect("a name").to_string())
            .collect();
        assert!(!subs.is_empty());
        for sub in &subs {
            assert!(
                AdminAction::from_name(sub).is_some(),
                "`{sub}` is registered but is not an AdminAction — it would fall through the \
                 gate's action arm to the menu"
            );
        }
        // …and in the other direction: every action is actually registered.
        for action in AdminAction::ALL {
            assert!(
                subs.iter().any(|s| s == action.name()),
                "AdminAction::{action:?} is not registered on the Discord surface"
            );
        }
    }

    /// A split stake is VISIBLE: the highlighter groups near-equal, near-simultaneous stakes and
    /// reports exactly what splitting bought — the gap between the split weight and the weight
    /// the same money would have carried as one stake. That gap is the sybil gain, stated in the
    /// numbers rather than in prose.
    #[test]
    fn the_split_stake_highlighter_shows_what_splitting_bought() {
        fn row(addr: &str, contributed: u64, first_seen: i64) -> crate::db::PoolContribution {
            crate::db::PoolContribution {
                deposit_address: addr.to_string(),
                user: "1".to_string(),
                contributed,
                payments: 1,
                first_seen,
                last_seen: first_seen,
            }
        }

        // Four near-equal stakes minutes apart — one 4,000,000 stake split four ways.
        let split: Vec<crate::db::PoolContribution> = (0..4)
            .map(|i| row(&format!("addr{i}"), 1_000_000, 1_000 + i * 60))
            .collect();
        let weighted: Vec<(&crate::db::PoolContribution, u64)> = split
            .iter()
            .map(|r| (r, dregg_pay::quadratic_weight(r.contributed)))
            .collect();
        let clusters = split_stake_clusters(&weighted);
        assert_eq!(clusters.len(), 1, "the four are one cluster: {clusters:?}");
        assert_eq!(clusters[0].count, 4);
        // THE GAIN, exactly: 4 × isqrt(1e6) = 4000 as split, isqrt(4e6) = 2000 as one stake.
        assert_eq!(clusters[0].split_weight, 4_000);
        assert_eq!(clusters[0].merged_weight, 2_000);
        assert!(
            clusters[0].split_weight > clusters[0].merged_weight,
            "quadratic weight is sybil-FAVOURABLE — splitting must show as a gain"
        );

        // Honest negatives: very different sizes are not a cluster…
        let mixed = [row("a", 1_000_000, 1_000), row("b", 900_000_000, 1_060)];
        let mixed_w: Vec<(&crate::db::PoolContribution, u64)> = mixed
            .iter()
            .map(|r| (r, dregg_pay::quadratic_weight(r.contributed)))
            .collect();
        assert!(split_stake_clusters(&mixed_w).is_empty());

        // …and neither are equal stakes far apart in time (a patient adversary is NOT caught —
        // this is a highlighter, not a detector, and the surface says so).
        let patient = [
            row("a", 1_000_000, 0),
            row("b", 1_000_000, SPLIT_WINDOW_SECS * 3),
        ];
        let patient_w: Vec<(&crate::db::PoolContribution, u64)> = patient
            .iter()
            .map(|r| (r, dregg_pay::quadratic_weight(r.contributed)))
            .collect();
        assert!(
            split_stake_clusters(&patient_w).is_empty(),
            "the heuristic's blind spot is real and must not be papered over"
        );

        // A single contributor is never a cluster.
        let lone = [row("a", 1_000_000, 0)];
        let lone_w: Vec<(&crate::db::PoolContribution, u64)> = lone
            .iter()
            .map(|r| (r, dregg_pay::quadratic_weight(r.contributed)))
            .collect();
        assert!(split_stake_clusters(&lone_w).is_empty());
    }

    /// The pool view is READ-ONLY: it is not registered as a mutating action, and it carries no
    /// exclude/ban option. Excluding a contributor from a pool they paid into is a value decision
    /// that was not asked for.
    #[test]
    fn the_pool_view_is_read_only() {
        assert!(!AdminAction::Pool.mutates());
        let json = serde_json::to_value(register()).expect("serializes");
        let pool = json["options"]
            .as_array()
            .unwrap()
            .iter()
            .find(|o| o["name"] == "pool")
            .expect("the pool subcommand is registered");
        let options = pool
            .get("options")
            .and_then(|o| o.as_array())
            .map(Vec::as_slice)
            .unwrap_or_default();
        assert!(
            options.is_empty(),
            "the pool view takes no options — nothing to exclude, ban or adjust with, got {options:?}"
        );
    }

    /// The refusal says what it is and does not leak the admin roster or the action list.
    #[test]
    fn the_refusal_names_the_reason_without_leaking_the_roster() {
        let wire = serde_json::to_value(refusal_embed()).expect("embed serializes");
        let text = wire.to_string();
        assert!(text.contains("Admin only"), "{text}");
        assert!(text.contains("operator"), "{text}");
        assert!(
            !text.contains("192258292544700426") && !text.contains("ADMIN_DISCORD_ID"),
            "the refusal must not disclose who the admins are or how they are configured: {text}"
        );
    }

    /// The narrator picker offers the attested path FIRST and labels every other choice as a
    /// downgrade — the ordering is product-load-bearing, not cosmetic.
    #[test]
    fn the_narrator_picker_leads_with_the_attested_path() {
        assert_eq!(NARRATOR_BACKENDS[0].0, "chutes-tee");
        assert!(narrator_backend_is_attested(NARRATOR_BACKENDS[0].0));
        for (key, description) in &NARRATOR_BACKENDS[1..] {
            assert!(
                !narrator_backend_is_attested(key),
                "`{key}` must not claim attestation"
            );
            assert!(
                description.contains("UNATTESTED") || *key == "none",
                "`{key}` must be labelled as a downgrade: {description}"
            );
        }

        // The registered choices carry the same vocabulary the setting stores.
        let json = serde_json::to_value(register()).expect("serializes");
        let narrator = json["options"]
            .as_array()
            .unwrap()
            .iter()
            .find(|o| o["name"] == "narrator")
            .expect("the narrator subcommand");
        let backend_opt = narrator["options"]
            .as_array()
            .unwrap()
            .iter()
            .find(|o| o["name"] == "backend")
            .expect("the backend option");
        let values: Vec<&str> = backend_opt["choices"]
            .as_array()
            .expect("choices")
            .iter()
            .map(|c| c["value"].as_str().unwrap())
            .collect();
        assert_eq!(
            values[0], "chutes-tee",
            "the attested path is offered first"
        );
        for (key, _) in NARRATOR_BACKENDS {
            assert!(values.contains(key), "`{key}` is missing from the picker");
        }
    }
}
