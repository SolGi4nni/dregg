//! `/faucet`, `/leaderboard`, `/history` commands — social and community features.

use serenity::all::{
    CommandInteraction, Context, CreateCommand, CreateInteractionResponse,
    CreateInteractionResponseMessage, EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

/// Register the /faucet command.
pub fn register_faucet() -> CreateCommand {
    CreateCommand::new("faucet").description("Claim free DEC tokens (1 per hour)")
}

/// Register the /leaderboard command.
pub fn register_leaderboard() -> CreateCommand {
    CreateCommand::new("leaderboard").description("Show top DEC holders")
}

/// Register the /history command.
pub fn register_history() -> CreateCommand {
    CreateCommand::new("history").description("Show your transaction history")
}

/// Register the /activity command.
pub fn register_activity() -> CreateCommand {
    CreateCommand::new("activity").description("Show recent committed activity across the devnet")
}

/// Handle /faucet interaction.
pub async fn handle_faucet(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let embed = execute_faucet(state, command.user.id.get()).await;
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Claim test DEC from the faucet (the real turn behind `/faucet` and the
/// `/start` "Get test DEC" button): rate-limited to 1/hour, records the claim
/// and a leaderboard transaction. Returns the embed to show.
pub(crate) async fn execute_faucet(state: &BotState, user_id: u64) -> serenity::all::CreateEmbed {
    let discord_id = user_id.to_string();

    // Check cclerk exists.
    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            return embeds::warning_embed(
                "No Cipherclerk",
                "You need a cipherclerk to use the faucet. Use `/start` → **Create my cipherclerk** first.",
            );
        }
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    };

    // Check rate limit (1 per hour).
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64;

    match state.db.get_last_faucet_claim(&discord_id).await {
        Ok(Some(last_claim)) => {
            let elapsed = now - last_claim;
            if elapsed < 3600 {
                let remaining = 3600 - elapsed;
                let mins = remaining / 60;
                let secs = remaining % 60;
                return embeds::warning_embed(
                    "Rate Limited",
                    &format!(
                        "You can claim again in **{mins}m {secs}s**.\n\nThe faucet allows 1 claim per hour."
                    ),
                );
            }
        }
        Ok(None) => {} // First claim ever.
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    }

    // Request from devnet faucet.
    match state.devnet.faucet_request(&cell_id).await {
        Ok(amount) => {
            // Record the claim.
            let _ = state.db.set_faucet_claim(&discord_id, now).await;
            // Also record as a transaction for leaderboard.
            let _ = state
                .db
                .record_transaction("faucet", &discord_id, amount, "faucet")
                .await;

            embeds::success_embed("Faucet Claimed")
                .field("Amount", format!("{amount} DEC"), true)
                .field("Next Claim", "In 1 hour", true)
        }
        Err(e) => embeds::error_embed("Faucet Error", &e.user_message("request faucet tokens")),
    }
}

/// Handle /leaderboard interaction (NOT ephemeral — visible to all).
pub async fn handle_leaderboard(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    // Leaderboard is public — not ephemeral.
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(CreateInteractionResponseMessage::new()),
        )
        .await;

    match state.db.get_leaderboard(10).await {
        Ok(entries) => {
            if entries.is_empty() {
                let embed = embeds::dregg_embed("Leaderboard")
                    .description("No transactions recorded yet. Be the first to use `/faucet`!");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for (i, (user_id, total)) in entries.iter().enumerate() {
                let medal = match i {
                    0 => "\u{1f947}",
                    1 => "\u{1f948}",
                    2 => "\u{1f949}",
                    _ => "\u{25ab}\u{fe0f}",
                };
                let user_display = if user_id == "faucet" {
                    "Faucet".to_string()
                } else {
                    format!("<@{user_id}>")
                };
                description.push_str(&format!(
                    "{medal} **#{}** {user_display} — {total} DEC\n",
                    i + 1
                ));
            }

            // The board sums the bot's LOCAL ledger — say so, and hand over the chain
            // press: the most recent recorded receipts get a re-check button each, so the
            // totals' underlying transfers are spot-checkable against the live node
            // (backlog Tier-2 #13).
            let recent = state
                .db
                .get_recent_transactions(10)
                .await
                .unwrap_or_default();
            let hashes: Vec<&str> = recent.iter().map(|t| t.tx_hash.as_str()).collect();
            let rows = crate::commands::tx_recheck::recheck_rows(&hashes, 5);
            let mut receipt_lines = String::new();
            for tx in recent
                .iter()
                .filter(|t| crate::commands::tx_recheck::checkable(&t.tx_hash))
                .take(5)
            {
                receipt_lines.push_str(&format!(
                    "{} DEC — {}\n",
                    tx.amount,
                    crate::commands::tx_recheck::receipt_ref(&tx.tx_hash),
                ));
            }

            let mut embed = embeds::dregg_embed("Leaderboard")
                .description(description)
                .field(
                    "What this is",
                    "Totals summed from the bot's local ledger. Every transfer behind them \
                     committed as a real turn and recorded its chain receipt — the recent ones \
                     are below, each with a **⛓ re-check** press that asks the live node, not \
                     this bot's database.",
                    false,
                );
            if !receipt_lines.is_empty() {
                embed = embed.field("Recent receipts", receipt_lines, false);
            }
            let _ = command
                .edit_response(
                    &ctx.http,
                    EditInteractionResponse::new().embed(embed).components(rows),
                )
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Leaderboard Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /history interaction.
pub async fn handle_history(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let (embed, rows) = execute_history(state, command.user.id.get()).await;
    let _ = command
        .edit_response(
            &ctx.http,
            EditInteractionResponse::new().embed(embed).components(rows),
        )
        .await;
}

/// Build the caller's transaction history (the same read behind `/cipherclerk
/// history` and the menu's History button): the ledger rows plus their
/// re-check-against-the-chain press rows.
pub(crate) async fn execute_history(
    state: &BotState,
    user_id: u64,
) -> (
    serenity::all::CreateEmbed,
    Vec<serenity::all::CreateActionRow>,
) {
    let discord_id = user_id.to_string();

    // Ensure user has a cclerk.
    if !state.db.user_exists(&discord_id).await.unwrap_or(false) {
        let embed = embeds::warning_embed(
            "No Cipherclerk",
            "You need a cipherclerk to view history. Use `/help` → **Just create my cipherclerk** (or `/cipherclerk create`).",
        );
        return (embed, vec![]);
    }

    match state.db.get_user_transactions(&discord_id, 15).await {
        Ok(txs) => {
            if txs.is_empty() {
                let embed =
                    embeds::dregg_embed("Transaction History").description("No transactions yet.");
                return (embed, vec![]);
            }

            let mut description = String::new();
            for tx in &txs {
                let direction = if tx.from_user == discord_id {
                    let to_display = if tx.to_user == "faucet" {
                        "Faucet".to_string()
                    } else {
                        format!("<@{}>", tx.to_user)
                    };
                    format!("\u{1f4e4} Sent {} DEC to {to_display}", tx.amount)
                } else {
                    let from_display = if tx.from_user == "faucet" {
                        "Faucet".to_string()
                    } else {
                        format!("<@{}>", tx.from_user)
                    };
                    format!("\u{1f4e5} Received {} DEC from {from_display}", tx.amount)
                };
                // Every transfer row carries its committed turn's receipt reference — the
                // chain hash the transfer path recorded, not just the bot's bookkeeping
                // (backlog Tier-2 #13). Faucet rows have no chain receipt and say nothing.
                let receipt = if crate::commands::tx_recheck::checkable(&tx.tx_hash) {
                    format!(
                        " · receipt {}",
                        crate::commands::tx_recheck::receipt_ref(&tx.tx_hash)
                    )
                } else {
                    String::new()
                };
                description.push_str(&format!("{direction}\n<t:{}:R>{receipt}\n\n", tx.timestamp));
            }

            // The re-check presses: each button asks the LIVE node whether the recorded
            // hash is a committed turn on its receipt chain — the row's escape from
            // trust-the-bot's-sqlite (`commands::tx_recheck`).
            let hashes: Vec<&str> = txs.iter().map(|t| t.tx_hash.as_str()).collect();
            let rows = crate::commands::tx_recheck::recheck_rows(&hashes, 5);

            let mut embed = embeds::dregg_embed("Transaction History").description(description);
            if !rows.is_empty() {
                embed = embed.field(
                    "Verify it yourself",
                    "These rows render from the bot's local ledger — press **⛓ re-check** and \
                     the bot asks the live node whether that receipt is a committed turn on \
                     the chain, in front of you.",
                    false,
                );
            }
            (embed, rows)
        }
        Err(e) => (embeds::error_embed("History Error", &e.to_string()), vec![]),
    }
}

/// Handle /activity interaction — a public, read-only feed of recent
/// committed turns from the live node (`/api/events`). This is the social
/// "who's doing what on devnet" surface; it reads real node state, no local
/// bookkeeping.
pub async fn handle_activity(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    // Public — not ephemeral.
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(CreateInteractionResponseMessage::new()),
        )
        .await;

    let embed = execute_activity(state).await;
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Build the recent-committed-activity feed (the same live-node read behind
/// `/federation activity` and the menus' Live-activity button).
pub(crate) async fn execute_activity(state: &BotState) -> serenity::all::CreateEmbed {
    match state.devnet.get_recent_events(12, None).await {
        Ok(events) if events.is_empty() => embeds::dregg_embed("Devnet Activity").description(
            "No committed turns observed yet. Be the first — try `/cipherclerk faucet` or \
             `/cipherclerk send`.",
        ),
        Ok(events) => {
            let mut description = String::new();
            for event in &events {
                let who = event
                    .cell_id
                    .as_deref()
                    .map(|c| format!("`{}...`", &c[..12.min(c.len())]))
                    .unwrap_or_else(|| "—".to_string());
                let turn = event
                    .tx_hash
                    .as_deref()
                    .map(|h| format!(" `{}...`", &h[..10.min(h.len())]))
                    .unwrap_or_default();
                description.push_str(&format!(
                    "**{}** — {} — {who}{turn}\n",
                    event.event_type, event.summary,
                ));
            }
            embeds::dregg_embed("Devnet Activity")
                .description(description)
                .field("Events", events.len().to_string(), true)
                .field("Source", "Live node `/api/events` (committed turns)", true)
        }
        Err(e) => embeds::error_embed(
            "Activity Unavailable",
            &e.user_message("read the activity feed"),
        ),
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}
