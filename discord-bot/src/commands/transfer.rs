//! `/send` and `/tip` commands — transfer tokens between users.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::embeds;

/// Register the /send command.
pub fn register_send() -> CreateCommand {
    CreateCommand::new("send")
        .description("Send DEC tokens to another user")
        .add_option(
            CreateCommandOption::new(CommandOptionType::User, "user", "Recipient").required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Integer,
                "amount",
                "Amount of DEC to send",
            )
            .required(true)
            .min_int_value(1),
        )
}

/// Register the /tip command.
///
/// Retired from the slash surface (it duplicated `/send`); kept so it can be
/// re-registered if wanted.
#[allow(dead_code)]
pub fn register_tip() -> CreateCommand {
    CreateCommand::new("tip")
        .description("Tip DEC tokens to another user")
        .add_option(
            CreateCommandOption::new(CommandOptionType::User, "user", "Recipient").required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::Integer, "amount", "Amount of DEC to tip")
                .required(true)
                .min_int_value(1),
        )
}

/// Handle /send or /tip interactions (same logic).
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sender_id = command.user.id.get();

    defer_ephemeral(ctx, command).await;

    // Parse options.
    let recipient_user_id = command
        .data
        .options
        .iter()
        .find(|o| o.name == "user")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::User(uid) => Some(uid.get()),
            _ => None,
        });

    let amount = command
        .data
        .options
        .iter()
        .find(|o| o.name == "amount")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n as u64),
            _ => None,
        });

    let (recipient_id, amount) = match (recipient_user_id, amount) {
        (Some(r), Some(a)) => (r, a),
        _ => {
            let embed = embeds::error_embed("Invalid Arguments", "Usage: /send @user <amount>");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    if recipient_id == sender_id {
        let embed = embeds::error_embed("Invalid Transfer", "You cannot send tokens to yourself.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let embed = execute_transfer(state, sender_id, recipient_id, amount).await;
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Submit a real transfer turn (the turn behind both `/send` and the `/start`
/// "Send" button form): verify the sender's hosted cell, verify the recipient
/// has a cell, pre-flight the balance, then submit the canonical signed
/// conserving turn through the devnet. Returns the embed to show. The caller is
/// responsible for the self-send check (the slash command and the button form
/// both reject sending to yourself up front).
pub(crate) async fn execute_transfer(
    state: &BotState,
    sender_id: u64,
    recipient_id: u64,
    amount: u64,
) -> serenity::all::CreateEmbed {
    let sender_discord = sender_id.to_string();
    let recipient_discord = recipient_id.to_string();

    // Verify sender has a hosted cclerk. External links are receive-only until
    // a proper external signing flow exists.
    let sender_cell = match state.db.get_user_identity(&sender_discord).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => identity.cell_id,
        Ok(Some(identity)) => {
            return embeds::warning_embed(
                "External Signing Required",
                &format!(
                    "Your linked identity is `{}`. The Discord bot cannot sign transfers for external identities yet.",
                    identity.mode.as_str()
                ),
            );
        }
        Ok(None) => {
            return embeds::warning_embed(
                "No Wallet",
                "You don't have a wallet yet. Use `/start` → **Create my wallet** first.",
            );
        }
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    };

    // Verify recipient has a cclerk.
    let recipient_cell = match state.db.get_cell_id(&recipient_discord).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            return embeds::warning_embed(
                "Recipient Has No Wallet",
                &format!(
                    "<@{recipient_id}> does not have a dregg wallet yet. They need to `/start` → **Create my wallet** first."
                ),
            );
        }
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    };

    // Pre-flight balance check so the user gets a clear "top up" message rather
    // than a raw executor rejection. Best-effort: if the read fails we still try
    // the transfer (the executor remains the authority).
    if let Ok(balance) = state.devnet.get_balance(&sender_cell).await {
        if balance < amount {
            return embeds::warning_embed(
                "Insufficient Balance",
                &format!(
                    "You have **{balance} DEC** but tried to send **{amount} DEC**. Top up with `/start` → **Get test DEC**."
                ),
            );
        }
    }

    // Derive sender's cclerk and submit a canonical signed turn.
    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        sender_id,
        state.federation_id_bytes,
    );

    // Submit transfer to devnet.
    match state
        .devnet
        .submit_transfer_turn(&cclerk, &sender_cell, &recipient_cell, amount)
        .await
    {
        Ok(tx_hash) => {
            // Record locally.
            let _ = state
                .db
                .record_transaction(&sender_discord, &recipient_discord, amount, &tx_hash)
                .await;

            // Best-effort post-transfer balance for confirmation.
            let remaining = state
                .devnet
                .get_balance(&sender_cell)
                .await
                .ok()
                .map(|b| format!("{b} DEC"))
                .unwrap_or_else(|| "—".to_string());

            let receipt_link = format!(
                "[view on explorer]({}/turn/{})",
                state.devnet.explorer_base_url(),
                tx_hash
            );

            embeds::success_embed("Transfer Sent")
                .field("To", format!("<@{recipient_id}>"), true)
                .field("Amount", format!("{amount} DEC"), true)
                .field("Your Balance", remaining, true)
                .field(
                    "Tx Hash",
                    format!("`{}...`", &tx_hash[..16.min(tx_hash.len())]),
                    true,
                )
                .field("Receipt", receipt_link, false)
        }
        Err(e) => embeds::error_embed("Transfer Failed", &e.user_message("submit the transfer")),
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
