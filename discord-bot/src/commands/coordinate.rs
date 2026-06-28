//! `/coordinate @partner [task] [price]` — watch two agents cooperate over the
//! promise-pipeline and settle atomically.
//!
//! The invoker is the CONSUMER: they ask `@partner` (the PRODUCER) to perform a
//! task. The producer computes the result off-chain and hands the consumer a
//! PROMISE; the consumer PIPELINES its payment against that promise; and the whole
//! cooperation settles ATOMICALLY as one verified conserving fold (per-asset Σδ=0,
//! Lean-FFI cross-checked). The reply shows the promise handoff, the parallel
//! layering, the conserving post-balances, and the round hash.
//!
//! What is real vs. demo is documented on [`crate::coordinate_flow`]: the
//! coordination MECHANISM (promise handoff + atomic verified settle + conservation
//! + rollback) is real and proven; the per-agent WORK is a deterministic demo over
//! a seeded ledger.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, EditInteractionResponse,
};

use dregg_app_framework::ring_trade::CommitmentId;

use crate::BotState;
use crate::coordinate_flow::run_pair_round;
use crate::embeds;

/// Register `/coordinate`.
pub fn register() -> CreateCommand {
    CreateCommand::new("coordinate")
        .description(
            "Coordinate a task with another agent over the promise-pipeline (atomic settle)",
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::User,
                "partner",
                "The agent who will produce the result you need",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "task",
                "What you want them to do (e.g. 'render-report')",
            )
            .required(false),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Integer,
                "price",
                "The amount you'll pay for the result (default 30)",
            )
            .required(false),
        )
}

/// Handle `/coordinate`.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let mut partner_id: Option<u64> = None;
    let mut task = "render-report".to_string();
    let mut price: u64 = 30;
    for opt in &command.data.options {
        match (opt.name.as_str(), &opt.value) {
            ("partner", CommandDataOptionValue::User(uid)) => partner_id = Some(uid.get()),
            ("task", CommandDataOptionValue::String(v)) if !v.trim().is_empty() => {
                task = v.trim().to_string()
            }
            ("price", CommandDataOptionValue::Integer(v)) if *v > 0 => price = *v as u64,
            _ => {}
        }
    }

    let invoker_id = command.user.id.get();
    let Some(partner_id) = partner_id else {
        let embed = embeds::error_embed("No Partner", "Pick a partner agent to coordinate with.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };
    if partner_id == invoker_id {
        let embed = embeds::error_embed(
            "Need Two Agents",
            "Coordination needs a partner different from you.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    // Derive each agent's coordination identity from their custodial seed. The
    // invoker is the CONSUMER (pays); the partner is the PRODUCER (computes).
    let consumer = agent_id(&state.config.bot_secret, invoker_id);
    let producer = agent_id(&state.config.bot_secret, partner_id);

    // Fund the consumer generously for the demonstration round.
    let consumer_balance = price.saturating_mul(10).max(price);

    match run_pair_round(producer, consumer, &task, price, consumer_balance) {
        Ok(out) => {
            let layers = out
                .receipt
                .parallel_layers
                .iter()
                .map(|l| format!("[{}]", l.join(", ")))
                .collect::<Vec<_>>()
                .join(" → ");
            let producer_promise = &out.receipt.fills[0];
            let body = format!(
                "**<@{invoker_id}> (consumer)** asked **<@{partner_id}> (producer)** to do `{task}`.\n\n\
                 1. The producer computed the result off-chain and handed over a **promise** \
                 (`EventualRef` slot {slot}, fill `{fill}…`).\n\
                 2. The consumer **pipelined** its payment against that promise.\n\
                 3. The whole cooperation **settled atomically** through the verified executor \
                 (per-asset Σδ=0, Lean-FFI cross-checked) — only this step touched the chain.\n\n\
                 **Pipeline layers:** `{layers}`\n\
                 **Settled (conserved):** consumer `{cbal}` · producer `{pbal}` · supply `{total}` (unchanged)\n\
                 **Round hash:** `{round}`\n\n\
                 _If either agent's work had failed, the promise would break and the round would roll back whole — nothing settles. The coordination mechanism is real + proven; the per-agent work is a deterministic demo over a seeded ledger (see `coordinate_flow`)._",
                slot = producer_promise.promise.output_slot,
                fill = &out.round_hash_hex()[..8],
                layers = layers,
                cbal = out.consumer_balance(),
                pbal = out.producer_balance(),
                total = out.conserved_total(),
                round = out.round_hash_hex(),
            );
            let embed =
                embeds::success_embed("🤝 Agents Coordinated — Atomic Settle").description(body);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Round Refused (atomic — nothing settled)",
                &format!("The coordination round refused, so no value moved: {e}"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Derive an agent's coordination identity (a [`CommitmentId`]) from the bot
/// secret + a Discord user id — the same custodial-seed derivation
/// [`crate::cipherclerk::seed_for`] uses for a user's cell.
fn agent_id(bot_secret: &[u8; 32], discord_user_id: u64) -> CommitmentId {
    CommitmentId(crate::cipherclerk::seed_for(bot_secret, discord_user_id))
}

/// Defer the response ephemerally while the round runs.
async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    use serenity::all::{CreateInteractionResponse, CreateInteractionResponseMessage};
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}
