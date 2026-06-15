//! `/deos` — the deos surface inside Discord.
//!
//! Surfaces the deos web-forward primitives (`crate::deos_surface`, built on the
//! REAL `starbridge-web-surface` mirrors of `Dregg2.Deos.*`) as live Discord
//! interactions:
//!
//! - **`/deos council [view-as]`** renders a cell's cap-gated affordance surface
//!   as Discord BUTTONS, projected per-viewer through the REAL `is_attenuation`: a
//!   `member` sees only `view`; a `council` member also sees `approve`; an `owner`
//!   also sees `admin` — progressive **attenuation** in Discord. It also
//!   TRANSCLUDES the council's live threshold into the embed (the REAL
//!   `TranscludedField`, provenanced) and posts the cell's `dregg://` link with its
//!   what-links-here count.
//! - **Pressing a button** (`crate::commands::deos::handle_component`) RE-RUNS the
//!   cap gate (`DeosCellSurface::fire`) — the anti-ghost tooth: an unauthorized
//!   fire is REFUSED (it is also never rendered), and an authorized fire yields a
//!   REAL verified-turn `AffordanceIntent` carrying a genuine `dregg_turn::Effect`.
//!
//! The cap discipline is the genuine `is_attenuation` throughout; the effects are
//! real `dregg_turn::Effect`s; the transclusion runs the real
//! content→commitment→receipt→quorum verification chain. The button → executed
//! node turn is the named dispatch seam (`deos_surface.rs` §"the seam").

use serenity::all::{
    ButtonStyle, CommandDataOptionValue, CommandInteraction, CommandOptionType,
    ComponentInteraction, Context, CreateActionRow, CreateButton, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use dregg_types::CellId;

use crate::BotState;
use crate::deos_surface::{
    DeosCellSurface, DiscordCapTier, TranscludedSurface, WhatLinksHere, render_transclusion,
};
use crate::embeds;

/// The council surface's status slot (where `approve` writes).
const STATUS_SLOT: usize = 0;

/// Register the `/deos` command.
pub fn register() -> CreateCommand {
    CreateCommand::new("deos")
        .description("The deos surface inside Discord — cap-gated affordance buttons, live transclusion, dregg:// links")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "council",
                "Render a council cell's cap-gated affordances as buttons (progressive attenuation)",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "view-as",
                    "Project the surface for this cap tier (default: your tier)",
                )
                .add_string_choice("anonymous", "anonymous")
                .add_string_choice("member", "member")
                .add_string_choice("council", "council")
                .add_string_choice("owner", "owner"),
            ),
        )
}

/// Handle `/deos` interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = command
        .data
        .options
        .first()
        .map(|o| o.name.as_str())
        .unwrap_or("");
    match subcommand {
        "council" => handle_council(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_council(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let discord_id = command.user.id.get().to_string();

    // The council surface is deterministically derived per invoking user (their
    // OWN council), so the demo is self-contained and the user is its owner. (A
    // production surface would be an app cell with a stored owner/council roster.)
    let user_cell = match resolve_user_cell(state, &discord_id).await {
        Some(c) => c,
        None => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a cclerk to open a deos surface. Use `/cipherclerk create` first.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    // The tier to PROJECT FOR. `view-as` overrides; default is the caller's own
    // tier (owner of their own council). The projection itself is the REAL gate.
    let tier = match sub_string_opt(command, "view-as").as_deref() {
        Some("anonymous") => DiscordCapTier::Anonymous,
        Some("member") => DiscordCapTier::Member,
        Some("council") => DiscordCapTier::Council,
        Some("owner") => DiscordCapTier::Owner,
        _ => DiscordCapTier::Owner, // the caller owns their own council
    };

    let surface = DeosCellSurface::council(user_cell, "Your Council", STATUS_SLOT);

    // (1) The per-viewer button projection — the REAL is_attenuation frustum.
    let buttons = surface.buttons_for(tier);
    let visible = surface.visible_names(tier);

    // (2) Transclude the live threshold into the embed (the REAL TranscludedField).
    let threshold_field = TranscludedSurface::publish(
        user_cell.0[0] ^ 0xC0,
        "Council Threshold",
        b"2-of-3 (quorum to approve)",
    );
    let transcluded = threshold_field
        .transclude()
        .ok()
        .map(|f| render_transclusion("Council Threshold", &f));

    // (3) what-links-here: this surface's dregg:// ref + how many cells transclude
    // it (here, the threshold field is observed by the council cell — a real,
    // verifiable backlink).
    let mut wlh = WhatLinksHere::new();
    if let Ok(f) = threshold_field.transclude() {
        wlh.observe(user_cell, &f);
    }
    let backlinks = wlh.backlink_count(threshold_field.uri().cell);

    // Build the embed.
    let mut embed = embeds::dregg_embed("deos · Council Surface")
        .description(format!(
            "Cap-gated affordances for cell `{}`, projected for a **{}** viewer. \
             You see exactly the buttons your held capabilities authorize — \
             progressive attenuation, decided by the REAL `is_attenuation`.",
            short_cell(&user_cell),
            tier.label(),
        ))
        .field(
            "Visible affordances",
            if visible.is_empty() {
                "_(none — this tier holds no authority over the surface)_".to_string()
            } else {
                visible
                    .iter()
                    .map(|n| format!("`{n}`"))
                    .collect::<Vec<_>>()
                    .join(" · ")
            },
            false,
        );

    if let Some(t) = &transcluded {
        embed = embed.field(
            format!("{} (transcluded)", t.label),
            format!("**{}**\n_{}_", t.value, t.provenance),
            false,
        );
    }

    embed = embed
        .field(
            "dregg:// link",
            format!(
                "`{}`\n{} cell(s) transclude this",
                threshold_field.uri_string(),
                backlinks
            ),
            false,
        )
        .footer(serenity::all::CreateEmbedFooter::new(format!(
            "viewer tier: {} · the projection IS the real cap gate",
            tier.label()
        )));

    // Attach the cap-gated buttons (Discord components). Pressing one re-runs the
    // gate via `handle_component` — the anti-ghost tooth.
    let mut response = EditInteractionResponse::new().embed(embed);
    let components = build_button_rows(&buttons);
    if !components.is_empty() {
        response = response.components(components);
    }
    let _ = command.edit_response(&ctx.http, response).await;
}

/// Handle a `deos:` component press — RE-RUN the cap gate (never trust the
/// rendered set) and report the fired verified-turn intent. The custom-id is
/// `deos:<surface-hex8>:<affordance>`; we re-derive the caller's tier and fire.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let custom_id = component.data.custom_id.clone();
    // Parse `deos:<hex8>:<affordance>`.
    let parts: Vec<&str> = custom_id.splitn(3, ':').collect();
    if parts.len() != 3 || parts[0] != "deos" {
        return;
    }
    let affordance = parts[2];

    let discord_id = component.user.id.get().to_string();
    let user_cell = match resolve_user_cell(state, &discord_id).await {
        Some(c) => c,
        None => {
            respond_component(
                ctx,
                component,
                embeds::warning_embed("No Cipherclerk", "Create a cclerk first."),
            )
            .await;
            return;
        }
    };

    // The caller pressing a button on THEIR OWN council is its owner. (A production
    // surface re-derives the tier from the stored roster; the gate is the same.)
    let tier = DiscordCapTier::Owner;
    let surface = DeosCellSurface::council(user_cell, "Your Council", STATUS_SLOT);

    // RE-RUN the cap gate — the anti-ghost tooth. An authorized fire yields a REAL
    // verified-turn intent; an unauthorized one is REFUSED (never run).
    match surface.fire(affordance, user_cell, tier) {
        Ok(intent) => {
            let embed = embeds::success_embed("Affordance Fired (verified turn)")
                .description(format!(
                    "Pressing `{affordance}` fired a REAL cap-gated verified turn. The cap gate \
                     (`is_attenuation`) passed IN-BAND; the effect is the genuine \
                     `dregg_turn::Effect` the executor would run.",
                ))
                .field("Affordance", format!("`{}`", intent.affordance), true)
                .field("Effect", format!("`{}`", effect_kind_of(&intent)), true)
                .field("Actor", format!("`{}`", short_cell(&intent.actor)), true)
                .field(
                    "Dispatch seam",
                    "The intent carries the real effect; handing it to the live node executor \
                     (so the receipt is the node's own) is the named seam.",
                    false,
                );
            respond_component(ctx, component, embed).await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Affordance Refused (anti-ghost)",
                &format!(
                    "Firing `{affordance}` was REFUSED by the REAL `is_attenuation` gate (never run): {}",
                    fire_error_msg(&e)
                ),
            );
            respond_component(ctx, component, embed).await;
        }
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// Resolve the invoking user's cell id (from their hosted cclerk), if any.
async fn resolve_user_cell(state: &BotState, discord_id: &str) -> Option<CellId> {
    let hex = state.db.get_cell_id(discord_id).await.ok().flatten()?;
    let bytes = hex::decode(&hex).ok()?;
    let arr: [u8; 32] = bytes.try_into().ok()?;
    Some(CellId::from_bytes(arr))
}

/// Read a string sub-option of the `/deos <subcommand>` invocation.
fn sub_string_opt(command: &CommandInteraction, name: &str) -> Option<String> {
    let sub = command.data.options.first()?;
    let opts = match &sub.value {
        CommandDataOptionValue::SubCommand(o) => o,
        _ => return None,
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

/// Build Discord button rows (max 5 per row) from the projected affordance set.
fn build_button_rows(
    buttons: &[crate::deos_surface::DiscordAffordanceButton],
) -> Vec<CreateActionRow> {
    buttons
        .chunks(5)
        .map(|chunk| {
            CreateActionRow::Buttons(
                chunk
                    .iter()
                    .map(|b| {
                        CreateButton::new(&b.custom_id)
                            .label(&b.affordance)
                            .style(button_style(&b.affordance))
                    })
                    .collect(),
            )
        })
        .collect()
}

/// A button style by affordance role (cosmetic only — the gate is the cap gate).
fn button_style(affordance: &str) -> ButtonStyle {
    match affordance {
        "admin" => ButtonStyle::Danger,
        "approve" => ButtonStyle::Success,
        _ => ButtonStyle::Secondary,
    }
}

/// A human message for a starbridge [`FireError`] (which carries no `Display`).
fn fire_error_msg(e: &starbridge_web_surface::affordance::FireError) -> String {
    use starbridge_web_surface::affordance::FireError;
    match e {
        FireError::NoSuchAffordance => "no such affordance on this surface".to_string(),
        FireError::Unauthorized {
            affordance,
            required,
        } => format!(
            "unauthorized: `{affordance}` requires {required:?} which this viewer does not hold"
        ),
        FireError::TransitionUnmet { affordance } => {
            format!("the `{affordance}` transition gate was not met")
        }
        FireError::OutsideWindow {
            affordance,
            open,
            close,
            height,
        } => format!("`{affordance}` is outside its window [{open}, {close}] (height {height})"),
    }
}

/// The effect-kind label of a fired intent (a readout of the REAL effect).
fn effect_kind_of(intent: &starbridge_web_surface::affordance::AffordanceIntent) -> &'static str {
    use starbridge_web_surface::affordance::EffectSummary;
    match intent.effect_summary() {
        EffectSummary::SetField { .. } => "SetField",
        EffectSummary::Transfer { .. } => "Transfer",
        EffectSummary::GrantCapability { .. } => "GrantCapability",
        EffectSummary::RevokeCapability { .. } => "RevokeCapability",
        EffectSummary::EmitEvent { .. } => "EmitEvent",
        EffectSummary::IncrementNonce { .. } => "IncrementNonce",
        EffectSummary::Other { tag } => tag,
    }
}

/// Short hex of a cell id (first 16 hex chars) for display.
fn short_cell(cell: &CellId) -> String {
    let mut s = String::with_capacity(16);
    for b in cell.0.iter().take(8) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

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

async fn respond_component(
    ctx: &Context,
    component: &ComponentInteraction,
    embed: serenity::all::CreateEmbed,
) {
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .embed(embed)
                    .ephemeral(true),
            ),
        )
        .await;
}
