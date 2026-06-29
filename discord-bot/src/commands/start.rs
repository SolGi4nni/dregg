//! `/start` and `/help` — the low-friction front door.
//!
//! This is the Telegram-style redesign of the bot's interaction model (see
//! `discord-bot/UX-REDESIGN.md`). Instead of memorising ~50 slash commands, a
//! user runs `/start`, gets a welcome + a small **button menu**, and from then on
//! mostly just **types** in their channel (the conversational Hermes loop in
//! [`crate::hermes_channel`]).
//!
//! Every action button fires the SAME real, cap-gated, receipted dregg turn the
//! corresponding slash command did — it calls the shared `execute_*` helpers
//! (`commands::cipherclerk::execute_create` / `execute_balance`,
//! `commands::social::execute_faucet`, `commands::transfer::execute_transfer`,
//! `commands::channel::execute_claim`, `commands::status::execute_status`,
//! `commands::key::store_key`). The affordance changed; the verification did not.

use serenity::all::{
    ActionRowComponent, ButtonStyle, CommandInteraction, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateCommand, CreateEmbed, CreateInputText,
    CreateInteractionResponse, CreateInteractionResponseMessage, CreateModal,
    EditInteractionResponse, InputTextStyle, ModalInteraction,
};

use crate::BotState;
use crate::embeds;
use crate::key_vault::PlaintextKey;
use crate::llm_provider::Provider;

// ─── component / modal custom-ids (the `start:` namespace) ───────────────────

const ID_HOME: &str = "start:home";
const ID_CREATE: &str = "start:create";
const ID_FAUCET: &str = "start:faucet";
// The guided "first 5 minutes" tour: identity → test DEC → one real paid turn.
const ID_TOUR: &str = "start:tour";
const ID_TOUR_IDENTITY: &str = "start:tour:identity";
const ID_TOUR_FAUCET: &str = "start:tour:faucet";
const ID_TOUR_FIRSTTURN: &str = "start:tour:firstturn";
const ID_BALANCE: &str = "start:balance";
const ID_SEND: &str = "start:send";
const ID_KEY: &str = "start:key";
const ID_CHANNEL: &str = "start:channel";
const ID_STATUS: &str = "start:status";
const ID_APPS: &str = "start:apps";
const ID_HELP: &str = "start:help";

const ID_MODAL_SEND: &str = "start:modal:send";
const ID_MODAL_KEY: &str = "start:modal:key";

const DEFAULT_TOKEN_BUDGET: i64 = 200_000;
const DEFAULT_RATE_LIMIT: i64 = 100;

/// The action a `start:` button maps to. Pure routing — unit tested below.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StartAction {
    Home,
    Create,
    Faucet,
    Balance,
    Send,
    Key,
    Channel,
    Status,
    Apps,
    Help,
    /// Open the guided first-5-minutes tour intro.
    Tour,
    /// Tour step 1 — create the newcomer's identity (a real cell).
    TourIdentity,
    /// Tour step 2 — fund it from the faucet.
    TourFaucet,
    /// Tour step 3 — the aha: a real, paid, verifiable first turn.
    TourFirstTurn,
    Unknown,
}

/// Map a component custom-id to its [`StartAction`]. Total + side-effect-free.
pub fn action_for(custom_id: &str) -> StartAction {
    match custom_id {
        ID_HOME => StartAction::Home,
        ID_CREATE => StartAction::Create,
        ID_FAUCET => StartAction::Faucet,
        ID_TOUR => StartAction::Tour,
        ID_TOUR_IDENTITY => StartAction::TourIdentity,
        ID_TOUR_FAUCET => StartAction::TourFaucet,
        ID_TOUR_FIRSTTURN => StartAction::TourFirstTurn,
        ID_BALANCE => StartAction::Balance,
        ID_SEND => StartAction::Send,
        ID_KEY => StartAction::Key,
        ID_CHANNEL => StartAction::Channel,
        ID_STATUS => StartAction::Status,
        ID_APPS => StartAction::Apps,
        ID_HELP => StartAction::Help,
        _ => StartAction::Unknown,
    }
}

// ─── slash registration ──────────────────────────────────────────────────────

/// Register `/start` — the onboarding entry point.
pub fn register() -> CreateCommand {
    CreateCommand::new("start")
        .description("Welcome to DreggNet — set up and get going (just click)")
}

/// Register `/help` — the map of the new model.
pub fn register_help() -> CreateCommand {
    CreateCommand::new("help").description("How to use the DreggNet bot — buttons + just typing")
}

// ─── /start ──────────────────────────────────────────────────────────────────

/// Handle `/start` — render the status-aware welcome + button menu.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let (embed, components) = home_view(state, user_id).await;
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(components)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

/// Handle `/help` — describe the model in one ephemeral message.
pub async fn handle_help(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(help_embed())
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

/// Build the welcome embed + the button menu, tailored to the user's state
/// (do they already have a wallet? a ported-in LLM key?).
async fn home_view(state: &BotState, user_id: u64) -> (CreateEmbed, Vec<CreateActionRow>) {
    let discord_id = user_id.to_string();
    let has_wallet = matches!(state.db.get_cell_id(&discord_id).await, Ok(Some(_)));
    let has_key = matches!(state.db.get_llm_key(&discord_id).await, Ok(Some(_)));

    let embed = if has_wallet {
        embeds::dregg_embed("Welcome back to DreggNet")
            .description(
                "Pick an action below, or **claim your channel and just type** — your messages \
                 become cap-gated, metered, receipted dregg turns under your own cell.",
            )
            .field("Wallet", "ready", true)
            .field("LLM key", if has_key { "set" } else { "not set" }, true)
    } else {
        embeds::dregg_embed("Welcome to DreggNet").description(
            "You're new here. The fastest way to *get* what DreggNet is: take the **2-minute tour** \
                 — it walks you to your first real, paid, verifiable thing on the network (get an \
                 identity \u{2192} get test DEC \u{2192} do one real turn \u{2192} here's your receipt). \
                 You barely need to learn any commands: click the buttons, or just type.",
        )
    };

    (embed, home_components(has_wallet, has_key))
}

/// The button menu. Newcomers (no wallet) see a single clear next step; everyone
/// else sees the common actions as an inline keyboard. Pure — unit tested below.
pub fn home_components(has_wallet: bool, has_key: bool) -> Vec<CreateActionRow> {
    if !has_wallet {
        return vec![CreateActionRow::Buttons(vec![
            button(ID_TOUR, "Start the 2-minute tour", ButtonStyle::Success),
            button(ID_CREATE, "Just create my wallet", ButtonStyle::Secondary),
            button(ID_STATUS, "Node status", ButtonStyle::Secondary),
            button(ID_HELP, "Help", ButtonStyle::Secondary),
        ])];
    }

    let key_label = if has_key {
        "Update my LLM key"
    } else {
        "Set my LLM key"
    };
    vec![
        CreateActionRow::Buttons(vec![
            button(ID_FAUCET, "Get test DEC", ButtonStyle::Success),
            button(ID_BALANCE, "Balance", ButtonStyle::Primary),
            button(ID_SEND, "Send", ButtonStyle::Primary),
            button(ID_CHANNEL, "Claim my channel", ButtonStyle::Primary),
        ]),
        CreateActionRow::Buttons(vec![
            button(ID_KEY, key_label, ButtonStyle::Secondary),
            button(ID_STATUS, "Node status", ButtonStyle::Secondary),
            button(ID_APPS, "Apps…", ButtonStyle::Secondary),
            button(ID_HELP, "Help", ButtonStyle::Secondary),
        ]),
    ]
}

fn help_embed() -> CreateEmbed {
    embeds::dregg_embed("Using the DreggNet bot")
        .description(
            "This bot is built to be light. There are really only two commands to remember:",
        )
        .field(
            "/start",
            "Onboard + the button menu for everything common.",
            false,
        )
        .field("/help", "This message.", false)
        .field(
            "Just type",
            "Claim your channel (`/start` → **Claim my channel**), then *type* in it. \
             `read <path>`, `search <query>`, `fetch <url>`, `run <cmd>`, `write <path>`, or plain \
             chat (routed through your own LLM key when set). Every message is a cap-gated, \
             metered, receipted dregg turn.",
            false,
        )
        .field(
            "Buttons do the rest",
            "Get test DEC · Balance · Send · Set your LLM key · Node status · Apps (Identity, \
             Names, Governance, Subscription).",
            false,
        )
        .field(
            "Power users",
            "Advanced surfaces are still slash commands: `/dregg` (app dashboard), `/explorer`, \
             `/cipherclerk` (keychain), `/cap-*` (CapTP), `/handoff`, `/coordinate`, `/deos`, \
             `/card`, `/proof`, federation + polis commands.",
            false,
        )
}

// ─── the guided first-5-minutes tour ─────────────────────────────────────────

/// The tour intro — what DreggNet Cloud offers + the three steps ahead.
fn tour_intro_embed() -> CreateEmbed {
    embeds::dregg_embed("The 2-minute tour")
        .description(
            "DreggNet Cloud is a small, live network where **you, or your agent, run real metered \
             work bounded by a capability you hold, and every run leaves a verifiable receipt**. \
             It offers four things: durable metered cap-gated **compute**, a **BYO-key Hermes** you \
             drive by typing, **agent coordination** that settles atomically, and **verifiable \
             receipts** anyone can check.\n\n\
             This tour walks you to your first real one. Three steps, ~2 minutes:",
        )
        .field("1. Get an identity", "A real dregg cell that's yours (custodial).", false)
        .field("2. Get test DEC", "Free, subsidized test tokens so you can actually do something.", false)
        .field(
            "3. Do one real thing",
            "A real, **paid**, **conserving** turn on the network — and a receipt you can verify.",
            false,
        )
        .field(
            "Honest state",
            "Early/alpha: a small devnet on subsidized compute. The step-3 turn needs the edge node \
             up; the tour tells you if it's recovering and never loses your place.",
            false,
        )
}

/// Tour intro buttons: begin, or skip to the plain menu.
fn tour_intro_components() -> Vec<CreateActionRow> {
    vec![CreateActionRow::Buttons(vec![
        button(
            ID_TOUR_IDENTITY,
            "Step 1: Get my identity",
            ButtonStyle::Success,
        ),
        button(ID_HOME, "Skip to the menu", ButtonStyle::Secondary),
    ])]
}

/// Buttons shown after a tour step completes, pointing to the next step.
fn tour_next_components(next: StartAction) -> Vec<CreateActionRow> {
    let row = match next {
        StartAction::TourFaucet => vec![
            button(ID_TOUR_FAUCET, "Step 2: Get test DEC", ButtonStyle::Success),
            button(ID_HOME, "Menu", ButtonStyle::Secondary),
        ],
        StartAction::TourFirstTurn => vec![
            button(
                ID_TOUR_FIRSTTURN,
                "Step 3: Do one real thing",
                ButtonStyle::Success,
            ),
            button(ID_HOME, "Menu", ButtonStyle::Secondary),
        ],
        // After the final step (or a retry prompt): offer the channel + retry.
        _ => vec![
            button(ID_CHANNEL, "Claim my channel", ButtonStyle::Primary),
            button(
                ID_TOUR_FIRSTTURN,
                "Try the turn again",
                ButtonStyle::Secondary,
            ),
            button(ID_HOME, "Menu", ButtonStyle::Secondary),
        ],
    };
    vec![CreateActionRow::Buttons(row)]
}

// ─── component routing (`start:` prefix, dispatched from main.rs) ────────────

/// Route a `start:` button press.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    match action_for(&component.data.custom_id) {
        // In-place re-renders of the same (ephemeral) menu message.
        StartAction::Home => {
            let (embed, components) = home_view(state, component.user.id.get()).await;
            update_message(ctx, component, embed, components).await;
        }
        StartAction::Apps => {
            // Hand off to the rich /dregg dashboard, in-place. Its subsequent
            // `dregg:*` component ids route to `dashboard::handle_component`.
            let embed =
                crate::commands::dashboard::home_embed(component.user.id.get(), state).await;
            let components = crate::commands::dashboard::home_components();
            update_message(ctx, component, embed, components).await;
        }
        StartAction::Help => {
            update_message(
                ctx,
                component,
                help_embed(),
                vec![CreateActionRow::Buttons(vec![button(
                    ID_HOME,
                    "Back",
                    ButtonStyle::Secondary,
                )])],
            )
            .await;
        }

        // The guided tour. The intro is an in-place re-render; each step defers,
        // fires the same real turn the corresponding button does, then offers the
        // next step so a newcomer cannot get lost.
        StartAction::Tour => {
            update_message(ctx, component, tour_intro_embed(), tour_intro_components()).await;
        }
        StartAction::TourIdentity => {
            defer_followup(ctx, component).await;
            let embed =
                crate::commands::cipherclerk::execute_create(state, component.user.id.get()).await;
            edit_followup_with(
                ctx,
                component,
                embed,
                tour_next_components(StartAction::TourFaucet),
            )
            .await;
        }
        StartAction::TourFaucet => {
            defer_followup(ctx, component).await;
            let embed =
                crate::commands::social::execute_faucet(state, component.user.id.get()).await;
            edit_followup_with(
                ctx,
                component,
                embed,
                tour_next_components(StartAction::TourFirstTurn),
            )
            .await;
        }
        StartAction::TourFirstTurn => {
            defer_followup(ctx, component).await;
            let embed =
                crate::commands::transfer::execute_first_payment(state, component.user.id.get())
                    .await;
            // The final screen offers the channel + a retry (covers a node outage).
            edit_followup_with(
                ctx,
                component,
                embed,
                tour_next_components(StartAction::Home),
            )
            .await;
        }

        // Modal-opening actions.
        StartAction::Send => open_modal(ctx, component, send_modal()).await,
        StartAction::Key => open_modal(ctx, component, key_modal()).await,

        // Network-backed actions: defer an ephemeral follow-up, then post the
        // result of the real turn (the menu message stays put).
        StartAction::Create => {
            defer_followup(ctx, component).await;
            let embed =
                crate::commands::cipherclerk::execute_create(state, component.user.id.get()).await;
            edit_followup(ctx, component, embed).await;
        }
        StartAction::Faucet => {
            defer_followup(ctx, component).await;
            let embed =
                crate::commands::social::execute_faucet(state, component.user.id.get()).await;
            edit_followup(ctx, component, embed).await;
        }
        StartAction::Balance => {
            defer_followup(ctx, component).await;
            let embed =
                crate::commands::cipherclerk::execute_balance(state, component.user.id.get()).await;
            edit_followup(ctx, component, embed).await;
        }
        StartAction::Status => {
            defer_followup(ctx, component).await;
            let embed = crate::commands::status::execute_status(state).await;
            edit_followup(ctx, component, embed).await;
        }
        StartAction::Channel => {
            defer_followup(ctx, component).await;
            let embed = match component.guild_id {
                Some(guild_id) => {
                    crate::commands::channel::execute_claim(ctx, guild_id, &component.user, state)
                        .await
                }
                None => embeds::warning_embed(
                    "Run In A Server",
                    "Claiming a channel needs a DreggNet server — open `/start` there, not in a DM.",
                ),
            };
            edit_followup(ctx, component, embed).await;
        }

        StartAction::Unknown => {
            defer_followup(ctx, component).await;
            edit_followup(
                ctx,
                component,
                embeds::warning_embed(
                    "Unknown Control",
                    "This control isn't recognised by this bot build.",
                ),
            )
            .await;
        }
    }
}

// ─── modals ──────────────────────────────────────────────────────────────────

fn send_modal() -> CreateModal {
    CreateModal::new(ID_MODAL_SEND, "Send DEC").components(vec![
        text_row(
            "recipient",
            "Recipient (@mention or user id)",
            "@alice or 123456789012345678",
        ),
        text_row("amount", "Amount (DEC)", "10"),
    ])
}

fn key_modal() -> CreateModal {
    CreateModal::new(ID_MODAL_KEY, "Set your LLM key").components(vec![
        text_row(
            "provider",
            "Provider",
            "anthropic / openai / openrouter / kimi / deepseek",
        ),
        text_row("key", "API key (sealed at rest, never echoed)", "sk-..."),
        text_row("model", "Model (optional)", "provider default"),
    ])
}

/// Route a `start:` modal submission.
pub async fn handle_modal(ctx: &Context, modal: &ModalInteraction, state: &BotState) {
    let embed = match modal.data.custom_id.as_str() {
        ID_MODAL_SEND => submit_send(state, modal).await,
        ID_MODAL_KEY => submit_key(state, modal).await,
        _ => embeds::warning_embed(
            "Unknown Form",
            "This form isn't recognised by this bot build.",
        ),
    };
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = modal
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

async fn submit_send(state: &BotState, modal: &ModalInteraction) -> CreateEmbed {
    let sender_id = modal.user.id.get();
    let recipient_raw = modal_value(modal, "recipient");
    let amount_raw = modal_value(modal, "amount");

    let recipient_id = match parse_user_id(&recipient_raw) {
        Some(id) => id,
        None => {
            return embeds::warning_embed(
                "Invalid Recipient",
                "Enter a recipient as an @mention or their numeric Discord user id.",
            );
        }
    };
    let amount = match parse_amount(&amount_raw) {
        Ok(a) => a,
        Err(msg) => return embeds::warning_embed("Invalid Amount", &msg),
    };
    if recipient_id == sender_id {
        return embeds::warning_embed("Invalid Transfer", "You cannot send tokens to yourself.");
    }

    // The SAME real conserving transfer turn the `/send` slash command fires.
    crate::commands::transfer::execute_transfer(state, sender_id, recipient_id, amount).await
}

async fn submit_key(state: &BotState, modal: &ModalInteraction) -> CreateEmbed {
    let owner = modal.user.id.get();
    let provider_raw = modal_value(modal, "provider");
    let provider = match Provider::parse(&provider_raw) {
        Some(p) => p,
        None if provider_raw.trim().is_empty() => Provider::Anthropic,
        None => {
            return embeds::warning_embed(
                "Unknown Provider",
                "Use one of: anthropic, openai, openrouter, kimi, deepseek.",
            );
        }
    };
    let key = PlaintextKey::new(modal_value(modal, "key"));
    if key.is_empty() {
        return embeds::warning_embed("Empty Key", "The API key must not be empty.");
    }
    let model = {
        let m = modal_value(modal, "model");
        if m.trim().is_empty() {
            provider.default_model().to_string()
        } else {
            m
        }
    };

    // The SAME sealing path the `/key set` slash command uses.
    match crate::commands::key::store_key(
        state,
        owner,
        provider,
        &model,
        &key,
        DEFAULT_TOKEN_BUDGET,
        DEFAULT_RATE_LIMIT,
    )
    .await
    {
        Ok(fingerprint) => {
            crate::commands::key::reset_session(state, owner);
            embeds::success_embed("Key Stored")
                .description(format!(
                    "Your **{}** key is sealed (encrypted at rest, never logged). Just chat in your \
                     channel — conversational messages route through it, metered + receipted.",
                    provider.display_name()
                ))
                .field("Provider", format!("`{}`", provider.as_str()), true)
                .field("Model", format!("`{model}`"), true)
                .field("Key", format!("`{fingerprint}`"), true)
        }
        Err(msg) => embeds::warning_embed("Could Not Store Key", &msg),
    }
}

// ─── pure helpers (unit tested) ──────────────────────────────────────────────

/// Parse a recipient from an @mention (`<@123>` / `<@!123>`) or a raw numeric id.
pub fn parse_user_id(raw: &str) -> Option<u64> {
    let trimmed = raw.trim();
    let digits: String = trimmed
        .trim_start_matches("<@!")
        .trim_start_matches("<@")
        .trim_end_matches('>')
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    if digits.is_empty() {
        // Allow a bare run of digits anywhere (e.g. pasted id with stray spaces).
        let bare: String = trimmed.chars().filter(|c| c.is_ascii_digit()).collect();
        return bare.parse().ok();
    }
    digits.parse().ok()
}

/// Parse a positive DEC amount.
pub fn parse_amount(raw: &str) -> Result<u64, String> {
    let trimmed = raw.trim();
    match trimmed.parse::<u64>() {
        Ok(0) => Err("Amount must be at least 1 DEC.".to_string()),
        Ok(n) => Ok(n),
        Err(_) => Err(format!("`{trimmed}` is not a whole number of DEC.")),
    }
}

fn modal_value(modal: &ModalInteraction, id: &str) -> String {
    for row in &modal.data.components {
        for component in &row.components {
            if let ActionRowComponent::InputText(input) = component {
                if input.custom_id == id {
                    return input.value.clone().unwrap_or_default().trim().to_string();
                }
            }
        }
    }
    String::new()
}

// ─── discord response plumbing ───────────────────────────────────────────────

fn button(id: &str, label: &str, style: ButtonStyle) -> CreateButton {
    CreateButton::new(id).label(label).style(style)
}

fn text_row(id: &str, label: &str, placeholder: &str) -> CreateActionRow {
    CreateActionRow::InputText(
        CreateInputText::new(InputTextStyle::Short, label, id)
            .placeholder(placeholder)
            .required(id != "model")
            .max_length(256),
    )
}

async fn update_message(
    ctx: &Context,
    component: &ComponentInteraction,
    embed: CreateEmbed,
    components: Vec<CreateActionRow>,
) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(components);
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::UpdateMessage(msg))
        .await;
}

async fn open_modal(ctx: &Context, component: &ComponentInteraction, modal: CreateModal) {
    let _ = component
        .create_response(&ctx.http, CreateInteractionResponse::Modal(modal))
        .await;
}

async fn defer_followup(ctx: &Context, component: &ComponentInteraction) {
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}

async fn edit_followup(ctx: &Context, component: &ComponentInteraction, embed: CreateEmbed) {
    let _ = component
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Like [`edit_followup`] but also carries the next-step buttons (used by the
/// guided tour so each completed step offers the next one).
async fn edit_followup_with(
    ctx: &Context,
    component: &ComponentInteraction,
    embed: CreateEmbed,
    components: Vec<CreateActionRow>,
) {
    let _ = component
        .edit_response(
            &ctx.http,
            EditInteractionResponse::new()
                .embed(embed)
                .components(components),
        )
        .await;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn custom_ids_route_to_actions() {
        assert_eq!(action_for("start:create"), StartAction::Create);
        assert_eq!(action_for("start:faucet"), StartAction::Faucet);
        assert_eq!(action_for("start:balance"), StartAction::Balance);
        assert_eq!(action_for("start:send"), StartAction::Send);
        assert_eq!(action_for("start:key"), StartAction::Key);
        assert_eq!(action_for("start:channel"), StartAction::Channel);
        assert_eq!(action_for("start:status"), StartAction::Status);
        assert_eq!(action_for("start:apps"), StartAction::Apps);
        assert_eq!(action_for("start:help"), StartAction::Help);
        assert_eq!(action_for("start:home"), StartAction::Home);
        // The guided tour routes the intro + each of its three steps.
        assert_eq!(action_for("start:tour"), StartAction::Tour);
        assert_eq!(action_for("start:tour:identity"), StartAction::TourIdentity);
        assert_eq!(action_for("start:tour:faucet"), StartAction::TourFaucet);
        assert_eq!(
            action_for("start:tour:firstturn"),
            StartAction::TourFirstTurn
        );
        // Foreign ids (e.g. the dashboard's) are not ours.
        assert_eq!(action_for("dregg:home"), StartAction::Unknown);
        assert_eq!(action_for("deosturn:transfer:1"), StartAction::Unknown);
    }

    #[test]
    fn newcomer_menu_is_a_single_clear_step() {
        // No wallet → one row, the tour leading, within Discord's 5-per-row limit.
        let rows = home_components(false, false);
        assert_eq!(rows.len(), 1, "newcomers see a single uncluttered row");
        if let CreateActionRow::Buttons(b) = &rows[0] {
            assert!(b.len() <= 5, "at most 5 buttons per action row");
        } else {
            panic!("newcomer row is a button row");
        }
    }

    #[test]
    fn tour_steps_chain_to_the_next_step() {
        // The intro offers a single clear "begin" row; each step's follow-up
        // offers the next step — a can't-get-lost chain. (Structural check; the
        // button ids themselves are routed by `action_for`, tested above.)
        assert_eq!(tour_intro_components().len(), 1);
        assert_eq!(tour_next_components(StartAction::TourFaucet).len(), 1);
        assert_eq!(tour_next_components(StartAction::TourFirstTurn).len(), 1);
        // The terminal screen (any non-step target) offers channel + retry + menu.
        if let CreateActionRow::Buttons(b) = &tour_next_components(StartAction::Home)[0] {
            assert_eq!(b.len(), 3, "final screen: channel, retry, menu");
        } else {
            panic!("final tour row is a button row");
        }
    }

    #[test]
    fn returning_user_menu_has_the_common_actions() {
        // Has wallet → two rows of common actions (8 buttons, all within
        // Discord's 5-per-row / 5-row limits).
        let rows = home_components(true, false);
        assert_eq!(rows.len(), 2);
        for row in &rows {
            if let CreateActionRow::Buttons(b) = row {
                assert!(b.len() <= 5, "at most 5 buttons per action row");
            } else {
                panic!("home menu rows are button rows");
            }
        }
    }

    #[test]
    fn parse_user_id_accepts_mentions_and_ids() {
        assert_eq!(parse_user_id("<@123456789>"), Some(123456789));
        assert_eq!(parse_user_id("<@!987654321>"), Some(987654321));
        assert_eq!(parse_user_id("  555000111  "), Some(555000111));
        assert_eq!(parse_user_id("not-a-user"), None);
        assert_eq!(parse_user_id(""), None);
    }

    #[test]
    fn parse_amount_rejects_zero_and_garbage() {
        assert_eq!(parse_amount("10"), Ok(10));
        assert_eq!(parse_amount("  42 "), Ok(42));
        assert!(parse_amount("0").is_err());
        assert!(parse_amount("-3").is_err());
        assert!(parse_amount("abc").is_err());
    }
}
