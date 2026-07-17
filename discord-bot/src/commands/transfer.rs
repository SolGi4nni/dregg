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
                "No Cipherclerk",
                "You don't have a cipherclerk yet. Use `/start` → **Create my cipherclerk** first.",
            );
        }
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    };

    // Verify recipient has a cclerk.
    let recipient_cell = match state.db.get_cell_id(&recipient_discord).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            return embeds::warning_embed(
                "Recipient Has No Cipherclerk",
                &format!(
                    "<@{recipient_id}> does not have a dregg cipherclerk yet. They need to `/start` → **Create my cipherclerk** first."
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

            // Explorer link when DREGG_EXPLORER_BASE is configured + the FULL turn
            // hash in a copyable block (the always-works verify-it-yourself handle).
            let receipt = crate::explorer_link::receipt_field("turn", &tx_hash, "view on explorer");

            embeds::success_embed("Transfer Sent")
                .field("To", format!("<@{recipient_id}>"), true)
                .field("Amount", format!("{amount} DEC"), true)
                .field("Your Balance", remaining, true)
                .field("Receipt (turn hash)", receipt, false)
        }
        Err(e) => embeds::error_embed("Transfer Failed", &e.user_message("submit the transfer")),
    }
}

// ─── The guided "first real turn" (the /start tour's aha step) ───────────────

/// The deterministic sentinel id the DreggNet **community cell** is derived from,
/// via the same custodial derivation a user cell uses. No real Discord snowflake
/// is `0`, so this never collides with a member's cell. It is the recipient of a
/// newcomer's first guided turn — a real, conserving payment they can verify.
const COMMUNITY_CELL_SENTINEL: u64 = 0;

/// The amount of test DEC the guided first turn pays the community cell. Small
/// enough that the faucet grant (1000 DEC) trivially covers it, large enough to
/// be a real conserving transfer the executor checks (Σδ=0).
pub(crate) const FIRST_TURN_AMOUNT: u64 = 5;

/// Fire the newcomer's **first real, paid, verifiable turn**: a small conserving
/// payment from their custodial cell to the DreggNet community cell, submitted as
/// a canonical signed dregg turn the node verifies end-to-end. On success the
/// embed carries the receipt (turn hash), an explorer link, and a portal link to
/// verify their own cell trustlessly in-browser. This is the same
/// `submit_transfer_turn` path `/send` uses — the affordance is guided, the
/// verification is unchanged.
///
/// This is the one step of the tour that needs the live edge node; on a node
/// outage it returns an honest "the node is recovering, everything up to here is
/// ready" message rather than a raw error, so the newcomer is never lost.
pub(crate) async fn execute_first_payment(
    state: &BotState,
    sender_id: u64,
) -> serenity::all::CreateEmbed {
    let sender_discord = sender_id.to_string();

    let sender_cell = match state.db.get_user_identity(&sender_discord).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => identity.cell_id,
        Ok(Some(_)) => {
            return embeds::warning_embed(
                "External Signing Required",
                "Your linked identity is external; the bot can't sign its turns yet. Create a hosted cipherclerk with `/start` → the tour first.",
            );
        }
        Ok(None) => {
            return embeds::warning_embed(
                "No Cipherclerk Yet",
                "Do the first two steps first: `/start` → **Create my identity**, then **Get test DEC**.",
            );
        }
        Err(e) => return embeds::error_embed("Database Error", &e.to_string()),
    };

    let community = UserCipherclerk::derive(
        &state.config.bot_secret,
        COMMUNITY_CELL_SENTINEL,
        state.federation_id_bytes,
    );
    let community_cell = community.cell_id_hex().to_string();

    // Best-effort materialize the community cell so the conserving transfer has a
    // valid destination. If the node is down this fails silently and the submit
    // below surfaces the honest node-recovering message.
    let _ = state
        .devnet
        .register_cell(&community_cell, community.public_key_hex())
        .await;

    // Pre-flight balance for a clear "get test DEC first" message.
    if let Ok(balance) = state.devnet.get_balance(&sender_cell).await {
        if balance < FIRST_TURN_AMOUNT {
            return embeds::warning_embed(
                "Get Test DEC First",
                &format!(
                    "You have **{balance} DEC** but this turn pays **{FIRST_TURN_AMOUNT} DEC**. Go back and tap **Get test DEC**."
                ),
            );
        }
    }

    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        sender_id,
        state.federation_id_bytes,
    );

    match state
        .devnet
        .submit_transfer_turn(&cclerk, &sender_cell, &community_cell, FIRST_TURN_AMOUNT)
        .await
    {
        Ok(tx_hash) => {
            let _ = state
                .db
                .record_transaction(
                    &sender_discord,
                    "dreggnet-community",
                    FIRST_TURN_AMOUNT,
                    &tx_hash,
                )
                .await;

            let explorer = crate::explorer_link::receipt_field(
                "turn",
                &tx_hash,
                "view the receipt on the explorer",
            );
            // The shared explorer-link rule (never a hardcoded maybe-dead URL): a cell
            // link when DREGG_EXPLORER_BASE is configured, the copyable cell id otherwise.
            let portal = crate::explorer_link::view_link(
                "cell",
                &sender_cell,
                "verify your cell in your own browser",
            );

            embeds::success_embed("\u{1f389} You just did a real, paid, verifiable thing")
                .description(format!(
                    "You paid **{FIRST_TURN_AMOUNT} DEC** to the DreggNet community cell as a real, \
                     **conserving** (Σδ=0), cap-gated dregg turn — signed by your own custodial key \
                     and verified by the node end-to-end. The same path `/send` uses.\n\n\
                     The **receipt** below is the proof it committed. Open it on the explorer, or open \
                     your cell there and let the in-browser light client re-verify your \
                     history — trusting no server.",
                ))
                .field(
                    "Receipt (turn hash)",
                    format!("`{}...`", &tx_hash[..16.min(tx_hash.len())]),
                    true,
                )
                .field("Paid", format!("{FIRST_TURN_AMOUNT} DEC"), true)
                .field("See it", explorer, false)
                .field("Verify it yourself", portal, false)
                .field(
                    "What next",
                    "Claim your channel and just **type** to drive a metered, receipted Hermes — or \
                     read `docs/GETTING-STARTED.md`.",
                    false,
                )
        }
        Err(e) => embeds::warning_embed(
            "This Step Needs the Edge Node",
            &format!(
                "{}\n\nEverything up to here is real and ready — your identity and test DEC are \
                 yours. The edge node is being brought back; tap **Try again** once **Node status** \
                 is green. (Meanwhile, claim your channel and type `read README.md` — the metered \
                 Hermes loop runs locally and doesn't need the node.)",
                e.user_message("submit your first turn")
            ),
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
