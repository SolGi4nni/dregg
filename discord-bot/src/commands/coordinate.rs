//! `/coordinate @partner [task] [price] [fail]` — watch two agents cooperate over
//! the promise-pipeline and settle atomically ON THE LIVE NODE.
//!
//! The invoker is the CONSUMER: they ask `@partner` (the PRODUCER) to perform a
//! task. The producer computes the result off-chain and hands the consumer a
//! PROMISE; the consumer PIPELINES its payment against that promise; and the whole
//! cooperation settles ATOMICALLY as ONE real conserving turn submitted to the
//! live node (per-asset Σδ=0, the node's verified executor re-checks it). The
//! reply shows the promise handoff, the parallel layering, the on-chain receipt
//! (turn hash + explorer link), and the conserving before/after balances of both
//! real cells.
//!
//! `fail: true` runs the broken-promise variant: the producer's work fails, the
//! promise breaks, and the round refuses BEFORE any settle — so nothing is
//! submitted to the node and both cells' live balances are unchanged (atomicity).
//!
//! What is real vs. demo is documented on [`crate::coordinate_flow`]: the
//! coordination MECHANISM (promise handoff + atomic on-chain settle + conservation
//! + rollback) is real and lands on the live node; the per-agent WORK is a
//! deterministic demo computation.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, EditInteractionResponse,
};

use dregg_app_framework::agent_coordination::CoordinationError;
use dregg_app_framework::ring_trade::CommitmentId;

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::coordinate_flow::{
    LiveSettle, run_pair_round, run_pair_round_broken, settle_round_live,
};
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
                "The amount of DEC you'll pay for the result (default 30)",
            )
            .required(false),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Boolean,
                "fail",
                "Simulate a broken promise — the round rolls back, nothing settles",
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
    let mut fail = false;
    for opt in &command.data.options {
        match (opt.name.as_str(), &opt.value) {
            ("partner", CommandDataOptionValue::User(uid)) => partner_id = Some(uid.get()),
            ("task", CommandDataOptionValue::String(v)) if !v.trim().is_empty() => {
                task = v.trim().to_string()
            }
            ("price", CommandDataOptionValue::Integer(v)) if *v > 0 => price = *v as u64,
            ("fail", CommandDataOptionValue::Boolean(v)) => fail = *v,
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

    // Derive each agent's REAL hosted cell. The invoker is the CONSUMER (pays);
    // the partner is the PRODUCER (computes). These are the same custodial cells
    // `/send` and the rest of the bot drive on the live node.
    let consumer_cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        invoker_id,
        state.federation_id_bytes,
    );
    let producer_cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        partner_id,
        state.federation_id_bytes,
    );
    let consumer = CommitmentId(consumer_cclerk.cell_id_bytes());
    let producer = CommitmentId(producer_cclerk.cell_id_bytes());
    let consumer_cell = consumer_cclerk.cell_id_hex().to_string();
    let producer_cell = producer_cclerk.cell_id_hex().to_string();

    // Materialize both cells on the node (idempotent), then ensure the consumer
    // can afford the settle. Best-effort: the node remains the authority.
    let _ = state
        .devnet
        .register_cell(&consumer_cell, consumer_cclerk.public_key_hex())
        .await;
    let _ = state
        .devnet
        .register_cell(&producer_cell, producer_cclerk.public_key_hex())
        .await;
    if let Ok(bal) = state.devnet.get_balance(&consumer_cell).await {
        if bal < price {
            let _ = state.devnet.faucet_request(&consumer_cell).await;
        }
    }

    // Read both cells' live balances BEFORE the round (the conservation witness).
    let c_before = state.devnet.get_balance(&consumer_cell).await.ok();
    let p_before = state.devnet.get_balance(&producer_cell).await.ok();

    // ── The broken-promise variant: the round rolls back, nothing settles ──
    if fail {
        let err = run_pair_round_broken(producer, consumer, &task);
        let downstream = match &err {
            CoordinationError::Broken {
                downstream_broken, ..
            } => downstream_broken.join(", "),
            _ => String::new(),
        };
        // Live atomicity: read balances AFTER — they must be unchanged because
        // the round refused before any turn was submitted.
        let c_after = state.devnet.get_balance(&consumer_cell).await.ok();
        let p_after = state.devnet.get_balance(&producer_cell).await.ok();
        let unchanged = c_before == c_after && p_before == p_after;
        let body = format!(
            "**<@{invoker_id}> (consumer)** asked **<@{partner_id}> (producer)** to do `{task}` — \
             but the producer's work **FAILED**.\n\n\
             1. The producer's promise **broke** ({err}).\n\
             2. The breakage propagated to the consumer's pipelined leg{downstream_note}.\n\
             3. The round **refused before any settle** — so **no turn was submitted to the node**.\n\n\
             **Live atomicity:** consumer `{cb}` → `{ca}` · producer `{pb}` → `{pa}` DEC \
             — {verdict}.\n\n\
             _A broken promise rolls the whole round back; the live ledger is untouched. \
             Run `/coordinate` without `fail` to watch the same pair settle atomically on-chain._",
            downstream_note = if downstream.is_empty() {
                String::new()
            } else {
                format!(" (`{downstream}`)")
            },
            cb = fmt_bal(c_before),
            ca = fmt_bal(c_after),
            pb = fmt_bal(p_before),
            pa = fmt_bal(p_after),
            verdict = if unchanged {
                "**unchanged** ✓ (rollback proven on the live node)"
            } else {
                "balances differ (node state moved independently)"
            },
        );
        let embed = embeds::warning_embed(
            "🔁 Promise Broke — Round Rolled Back (nothing settled)",
            &body,
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    // ── The success path: off-chain promise pipeline, then atomic on-chain settle ──
    let consumer_balance = price.saturating_mul(10).max(price);
    let out = match run_pair_round(producer, consumer, &task, price, consumer_balance) {
        Ok(out) => out,
        Err(e) => {
            let embed = embeds::error_embed(
                "Round Refused (off-chain — nothing settled)",
                &format!("The coordination round refused, so no value moved: {e}"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    // Submit the round's settle to the LIVE node as one atomic conserving turn.
    let memo = format!("coordinate {task} ({price} DEC)");
    match settle_round_live(&state.devnet, &consumer_cclerk, &out.receipt, memo).await {
        Ok(LiveSettle::Landed { turn_hash, .. }) => {
            let c_after = state.devnet.get_balance(&consumer_cell).await.ok();
            let p_after = state.devnet.get_balance(&producer_cell).await.ok();
            let layers = out
                .receipt
                .parallel_layers
                .iter()
                .map(|l| format!("[{}]", l.join(", ")))
                .collect::<Vec<_>>()
                .join(" → ");
            let producer_promise = &out.receipt.fills[0];
            let receipt_link = crate::explorer_link::view_link(
                "turn",
                &turn_hash,
                "view the receipt on the explorer",
            );
            let conserved = match (c_before, c_after, p_before, p_after) {
                (Some(cb), Some(ca), Some(pb), Some(pa)) => {
                    let before = cb.saturating_add(pb);
                    let after = ca.saturating_add(pa);
                    format!(
                        "consumer `{cb}` → `{ca}` · producer `{pb}` → `{pa}` · sum `{before}` → `{after}` {check}",
                        check = if before == after {
                            "(conserved ✓)"
                        } else {
                            ""
                        }
                    )
                }
                _ => "(balances read pending)".to_string(),
            };
            let body = format!(
                "**<@{invoker_id}> (consumer)** asked **<@{partner_id}> (producer)** to do `{task}`.\n\n\
                 1. The producer computed the result off-chain and handed over a **promise** \
                 (`EventualRef` slot {slot}, fill `{fill}…`).\n\
                 2. The consumer **pipelined** its payment against that promise.\n\
                 3. The whole cooperation **settled atomically on the live node** as one \
                 conserving turn (per-asset Σδ=0, the node's verified executor re-checked it).\n\n\
                 **Pipeline layers:** `{layers}`\n\
                 **Live balances (DEC):** {conserved}\n\
                 **On-chain receipt:** `{turn_short}…`\n\
                 **Round hash:** `{round}`\n\n\
                 {receipt_link}\n\n\
                 _The coordination mechanism — promise handoff, atomic settle, conservation, \
                 rollback — is real and landed on the live node. Try `/coordinate fail:true` to \
                 watch a broken promise roll the whole round back._",
                slot = producer_promise.promise.output_slot,
                fill = &out.round_hash_hex()[..8],
                turn_short = &turn_hash[..16.min(turn_hash.len())],
                round = out.round_hash_hex(),
            );
            let embed =
                embeds::success_embed("🤝 Agents Coordinated — Atomic Settle on the Live Node")
                    .description(body);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(LiveSettle::NothingToSettle) => {
            let embed = embeds::warning_embed(
                "Round Had No Value Moves",
                "The promise pipeline ran but the round settled no value, so nothing was submitted to the node.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Settle Refused (atomic — nothing committed)",
                &format!(
                    "The off-chain round succeeded, but the live settle did not land, so no value moved: {e}"
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Render an optional balance for display.
fn fmt_bal(b: Option<u64>) -> String {
    b.map(|v| v.to_string()).unwrap_or_else(|| "—".to_string())
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
