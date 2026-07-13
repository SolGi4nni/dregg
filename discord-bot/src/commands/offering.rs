//! **The generic DreggNet-offering → Discord adapter.**
//!
//! `/dungeon` (`commands::fiction`) proved one offering can be played in Discord. This module
//! is the *shape* of that proof, extracted: ANY [`dreggnet_offerings::Offering`] —
//! [`dreggnet_council::CouncilOffering`], [`dreggnet_market::MarketOffering`], a hosted-Hermes
//! or grain offering later — becomes a Discord command surface by implementing
//! [`DiscordOffering`] (a key, a title, a session store, and which turns take a typed value).
//!
//! The bot is the offering core's **Discord `Frontend`** in the sense
//! `dreggnet_offerings`'s doc names:
//!
//! * **present** — an offering's [`Offering::render`] returns a deos [`Surface`] (a
//!   `deos_view::ViewNode`). We paint it through the SAME `deos_view::discord` backend the
//!   desktop/web/seL4 renderers are peers of ([`embed_of`]) — the card is authored once by the
//!   offering and rendered by the platform. We keep only the *embed* from that render and mint
//!   the *components* ourselves ([`action_rows`]) from the typed [`Offering::actions`], because
//!   a Discord custom-id must carry **which offering** the press belongs to (`deos_view`'s
//!   `deosturn:<turn>:<arg>` id is already the `viewnode_applet` card route) and because some
//!   affordances need a **typed value** the user supplies in a modal.
//! * **collect** — a press decodes back into the typed `(SessionId, Action, DreggIdentity)`:
//!   [`parse_press`] → [`drive`] / [`drive_value`].
//! * **the actor is a real dregg identity** — never a Discord nickname. The presser's
//!   [`DreggIdentity`] is their derived Ed25519 public key hex
//!   (`UserCipherclerk::derive(bot_secret, user_id, federation)`), exactly as `/dungeon`'s
//!   ballots are attributed ([`identity_of`]).
//! * **the executor is the sole referee** — a press is ONE [`Offering::advance`]: a legal move
//!   lands a real `TurnReceipt` ([`Outcome::Landed`]), an illegal/ineligible/forged one is a
//!   real [`Outcome::Refused`] that commits nothing. A currently-ineligible affordance is
//!   rendered **locked but still pressable** (`🔒`, danger-styled) — the cap tooth is *shown,
//!   not hidden*, and pressing it surfaces the executor's own refusal honestly, rather than the
//!   frontend pretending to be the gate.
//!
//! ## The custom-id wire
//!
//! | id                                | meaning                                            |
//! |-----------------------------------|----------------------------------------------------|
//! | `offering:fire:<key>:<turn>:<arg>`| press → one `advance(Action{turn,arg}, actor)`      |
//! | `offering:ask:<key>:<turn>`       | press → open a modal for the turn's typed value     |
//! | `offering:submit:<key>:<turn>`    | the modal's submit → `advance` with the typed value |
//!
//! `<key>` is [`DiscordOffering::KEY`] (`council`, `market`, …) — the router in `main.rs` sends
//! every `offering:` press here, and [`route_component`] / [`route_modal`] dispatch on the key.
//!
//! ## What is logic-driven vs what needs a live Discord token
//!
//! [`drive`] / [`drive_value`] are the **sync core** of a press: decode the custom-id, resolve
//! the actor, run the real offering turn, hand back the [`Outcome`]. The async handlers
//! ([`handle_component`], [`handle_modal`], [`handle_status`], [`handle_verify`]) are thin
//! serenity wrappers around them. So the tests drive the SAME path a live button press takes —
//! only the HTTP round-trip to Discord is absent.

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};

use serenity::all::{
    ActionRowComponent, ButtonStyle, CommandInteraction, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateEmbed, CreateEmbedFooter, CreateInputText,
    CreateInteractionResponse, CreateInteractionResponseMessage, CreateModal, InputTextStyle,
    ModalInteraction,
};

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, Outcome, SessionConfig, Surface, VerifyReport,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;

/// The custom-id namespace every offering component press lives in (`main.rs` routes on it).
pub const PREFIX: &str = "offering";
/// The modal input field carrying an affordance's typed value (a reserve price, a sealed bid).
pub const VALUE_FIELD: &str = "value";

/// A **live offering in a channel** — the offering value itself (a council carries its
/// electorate/catalog/quorum; a market its pricing) plus its open session. Both are needed to
/// advance, so both are stored.
pub struct Live<O: Offering> {
    /// The offering (the stateless-ish factory that also carries the session-shaping config).
    pub offering: O,
    /// The live confined session (the real receipt chain).
    pub session: O::Session,
}

/// A turn whose [`Action::arg`] is a **number the user supplies** rather than a fixed index —
/// rendered as a button that opens a Discord modal (the market's reserve price / sealed bid).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValuePrompt {
    /// The modal title.
    pub title: &'static str,
    /// The input field's label.
    pub label: &'static str,
    /// The input field's placeholder.
    pub placeholder: &'static str,
}

/// A unit of work against an offering's live session table, run ON the store's owning thread.
type Job<O> = Box<dyn FnOnce(&mut HashMap<u64, Live<O>>) + Send + 'static>;

/// **The per-offering session store — a dedicated thread that OWNS the live sessions.**
///
/// Not a `Mutex<HashMap<…>>`, and for a load-bearing reason: an offering session is not
/// necessarily `Send`. [`dreggnet_council::CouncilSession`] holds `collective_choice::BallotCap`s,
/// each carrying a `Mandate` whose non-amplification predicate is an `Rc<dyn Fn(u64) -> bool>`
/// (`dregg-intent`'s `agent_mandate`) — so a council session cannot cross a thread boundary at
/// all, and a `static Mutex<…>` (which needs `Sync`, hence `Send` contents) will not hold one.
///
/// So the sessions are **confined to their store's thread** (fittingly: an offering session IS a
/// confined thing). Every access is a job shipped to that thread and awaited; the session itself
/// never moves. Only the *offering* (`O: Send` — a council's electorate/catalog/quorum) and the
/// job's *result* (an embed, an [`Outcome`], a [`VerifyReport`] — all plain data) cross.
///
/// A job is short and CPU-bound (one real executor turn), and the call blocks the caller until it
/// returns — the same cost profile as `/dungeon`'s `sessions()` mutex, which likewise resolves a
/// real turn while holding the lock. Nothing awaits inside a job, so no deadlock is reachable.
///
/// (Were `Mandate::admits` an `Arc<dyn Fn + Send + Sync>`, this could collapse back to a plain
/// `Mutex<HashMap<…>>`. That is a cross-crate change to `dregg-intent`, deliberately not made
/// here.)
pub struct Store<O: DiscordOffering> {
    jobs: SyncSender<Job<O>>,
}

impl<O: DiscordOffering> Store<O> {
    /// Spawn the store's owning thread (called once, from the offering's `store()` `OnceLock`).
    pub fn spawn() -> Store<O> {
        let (jobs, rx) = sync_channel::<Job<O>>(64);
        std::thread::Builder::new()
            .name(format!("offering-{}", O::KEY))
            .spawn(move || {
                let mut sessions: HashMap<u64, Live<O>> = HashMap::new();
                while let Ok(job) = rx.recv() {
                    job(&mut sessions);
                }
            })
            .expect("spawn the offering session thread");
        Store { jobs }
    }

    /// Run `f` against the session table on the owning thread and hand back its result.
    fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut HashMap<u64, Live<O>>) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |sessions| {
                let _ = tx.send(f(sessions));
            }))
            .expect("the offering session thread is alive");
        rx.recv().expect("the offering session thread answered")
    }
}

/// **An offering the bot serves as a Discord surface.** Implement this on any
/// [`Offering`] and the whole Discord frontend (embed, buttons, modals, press→turn, verify)
/// comes from this module.
pub trait DiscordOffering: Offering + Send + Sized + 'static
where
    Self::Session: 'static,
{
    /// The offering's key in the custom-id wire (`council`, `market`).
    const KEY: &'static str;
    /// The embed title.
    const TITLE: &'static str;
    /// The embed colour.
    const COLOR: u32;
    /// The honest footer tagline (what the surface actually guarantees).
    const TAGLINE: &'static str;

    /// The per-channel session store for this offering (one live session per channel), owned by
    /// its own thread. Implementors hand back a `OnceLock`-initialised [`Store::spawn`].
    fn store() -> &'static Store<Self>;

    /// Which turns take a user-supplied numeric arg (a modal), rather than a fixed one.
    fn value_prompt(_turn: &str) -> Option<ValuePrompt> {
        None
    }

    /// A one-line honest status ribbon (verified turns, phase, quorum) for the footer.
    fn status_line(&self, session: &Self::Session) -> String;
}

// ─────────────────────────────────────────────────────────────────────────────
// The session store.
// ─────────────────────────────────────────────────────────────────────────────

/// Open a fresh session for `channel` (fail-closed: an offering that refuses to deploy is
/// surfaced, never faked). The session is BORN on the store's thread, where it then lives.
/// Replaces any session already open in the channel.
pub fn open_in<O: DiscordOffering>(
    channel: u64,
    offering: O,
    cfg: SessionConfig,
) -> Result<(), dreggnet_offerings::OfferingError> {
    O::store().run(move |sessions| {
        let session = offering.open(cfg)?;
        sessions.insert(channel, Live { offering, session });
        Ok(())
    })
}

/// Whether `channel` has a live session of this offering.
pub fn is_open<O: DiscordOffering>(channel: u64) -> bool {
    O::store().run(move |sessions| sessions.contains_key(&channel))
}

/// Run `f` against the channel's live session (`None` when no session is open). `f` runs on the
/// store's thread; only its result comes back.
pub fn with_live<O: DiscordOffering, R: Send + 'static>(
    channel: u64,
    f: impl FnOnce(&mut Live<O>) -> R + Send + 'static,
) -> Option<R> {
    O::store().run(move |sessions| sessions.get_mut(&channel).map(f))
}

/// Drop the channel's session. Part of the adapter's session API (a `/<offering> close`
/// subcommand is the obvious next consumer); today the driven tests are what exercise it.
#[allow(dead_code)]
pub fn close_in<O: DiscordOffering>(channel: u64) {
    O::store().run(move |sessions| {
        sessions.remove(&channel);
    });
}

// ─────────────────────────────────────────────────────────────────────────────
// Identity — the actor is a derived dregg key, never a Discord nickname.
// ─────────────────────────────────────────────────────────────────────────────

/// The presser's **derived dregg identity** — their Ed25519 public key hex, deterministic in
/// `(bot_secret, discord_user_id, federation)`. The SAME derivation `/dungeon` attributes its
/// ballots to, and the SAME hex `CouncilOffering::member_identity` builds an electorate from.
pub fn identity_of(state: &BotState, discord_user_id: u64) -> DreggIdentity {
    DreggIdentity(
        UserCipherclerk::derive(
            &state.config.bot_secret,
            discord_user_id,
            state.federation_id_bytes,
        )
        .public_key_hex()
        .to_string(),
    )
}

/// The presser's raw Ed25519 public key (what a council electorate is built from).
pub fn public_key_of(state: &BotState, discord_user_id: u64) -> [u8; 32] {
    UserCipherclerk::derive(
        &state.config.bot_secret,
        discord_user_id,
        state.federation_id_bytes,
    )
    .app
    .public_key()
    .0
}

// ─────────────────────────────────────────────────────────────────────────────
// The custom-id wire.
// ─────────────────────────────────────────────────────────────────────────────

/// A decoded component press.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Press {
    /// Fire affordance `turn` with the fixed `arg` — one real offering turn.
    Fire {
        /// The offering key ([`DiscordOffering::KEY`]).
        key: String,
        /// The affordance verb.
        turn: String,
        /// The affordance argument.
        arg: i64,
    },
    /// The affordance needs a typed value: open the modal for `turn`.
    Ask {
        /// The offering key.
        key: String,
        /// The affordance verb whose value the modal collects.
        turn: String,
    },
}

/// The custom-id of a fixed-arg affordance button.
pub fn fire_id(key: &str, turn: &str, arg: i64) -> String {
    format!("{PREFIX}:fire:{key}:{turn}:{arg}")
}

/// The custom-id of a value-taking affordance button (opens the modal).
pub fn ask_id(key: &str, turn: &str) -> String {
    format!("{PREFIX}:ask:{key}:{turn}")
}

/// The custom-id of the modal that collects `turn`'s typed value.
pub fn submit_id(key: &str, turn: &str) -> String {
    format!("{PREFIX}:submit:{key}:{turn}")
}

/// Decode a component press. `None` for any id that is not ours.
pub fn parse_press(custom_id: &str) -> Option<Press> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "fire", key, turn, arg] => Some(Press::Fire {
            key: (*key).to_string(),
            turn: (*turn).to_string(),
            arg: arg.parse().ok()?,
        }),
        [PREFIX, "ask", key, turn] => Some(Press::Ask {
            key: (*key).to_string(),
            turn: (*turn).to_string(),
        }),
        _ => None,
    }
}

/// Decode a modal submit id into `(key, turn)`. `None` for any id that is not ours.
pub fn parse_submit(custom_id: &str) -> Option<(String, String)> {
    let parts: Vec<&str> = custom_id.split(':').collect();
    match parts.as_slice() {
        [PREFIX, "submit", key, turn] => Some(((*key).to_string(), (*turn).to_string())),
        _ => None,
    }
}

/// The offering key a press/submit id belongs to (what the router dispatches on).
pub fn key_of(custom_id: &str) -> Option<String> {
    match parse_press(custom_id) {
        Some(Press::Fire { key, .. }) | Some(Press::Ask { key, .. }) => Some(key),
        None => parse_submit(custom_id).map(|(k, _)| k),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — the offering's own deos Surface → a Discord embed + affordance buttons.
// ─────────────────────────────────────────────────────────────────────────────

/// The offering's [`Surface`] (its deos `ViewNode`) rendered to a Discord embed through the
/// `deos_view::discord` backend — the SAME renderer the desktop/web/framebuffer backends are
/// peers of. We take the embed only: the components come from [`action_rows`] (see the module
/// doc — a Discord custom-id must carry the offering key and route a value-taking affordance to
/// its modal, which the generic `deosturn:` card id cannot).
pub fn embed_of<O: DiscordOffering>(live: &Live<O>) -> CreateEmbed {
    let surface: Surface = live.offering.render(&live.session);
    let card = deos_view::discord::render_card(O::TITLE, surface.view(), &[]);
    card.embed
        .color(O::COLOR)
        .footer(CreateEmbedFooter::new(truncate(
            &format!(
                "{} · {}",
                live.offering.status_line(&live.session),
                O::TAGLINE
            ),
            2040,
        )))
}

/// The affordance buttons for the session's current [`Offering::actions`], chunked into Discord
/// rows (≤5 × ≤5).
///
/// * an **eligible** action → a primary button firing `(turn, arg)`;
/// * an action whose turn takes a **typed value** → a button that opens its modal;
/// * an **ineligible** action → `🔒`, danger-styled, and **still pressable**: the cap tooth is
///   shown, not hidden, and the press surfaces the executor's own [`Outcome::Refused`] rather
///   than the frontend pretending to be the gate.
pub fn action_rows<O: DiscordOffering>(actions: &[Action]) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for chunk in actions.chunks(5).take(5) {
        let mut buttons: Vec<CreateButton> = Vec::new();
        for a in chunk {
            let id = if O::value_prompt(&a.turn).is_some() {
                ask_id(O::KEY, &a.turn)
            } else {
                fire_id(O::KEY, &a.turn, a.arg)
            };
            let label = if a.enabled {
                truncate(&a.label, 78)
            } else {
                truncate(&format!("🔒 {}", a.label), 78)
            };
            let style = if a.enabled {
                ButtonStyle::Primary
            } else {
                ButtonStyle::Danger
            };
            buttons.push(CreateButton::new(id).label(label).style(style));
        }
        rows.push(CreateActionRow::Buttons(buttons));
    }
    rows
}

/// The full surface of a channel's live session: embed + affordance rows.
pub fn surface_of<O: DiscordOffering>(live: &Live<O>) -> (CreateEmbed, Vec<CreateActionRow>) {
    let actions = live.offering.actions(&live.session);
    (embed_of(live), action_rows::<O>(&actions))
}

/// The modal that collects a value-taking affordance's typed arg.
pub fn value_modal<O: DiscordOffering>(turn: &str, prompt: ValuePrompt) -> CreateModal {
    CreateModal::new(submit_id(O::KEY, turn), prompt.title).components(vec![
        CreateActionRow::InputText(
            CreateInputText::new(InputTextStyle::Short, prompt.label, VALUE_FIELD)
                .placeholder(prompt.placeholder)
                .required(true)
                .max_length(20),
        ),
    ])
}

/// An honest account of a resolved move: a landed receipt (with its real `turn_hash`) or the
/// executor's own refusal reason — never laundered.
pub fn outcome_note(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Landed { receipt, ended } => {
            let h = hex::encode(&receipt.turn_hash[..8]);
            let tail = if *ended {
                " — the session ended."
            } else {
                ""
            };
            format!("**A verified turn landed.** `turn_hash {h}…`{tail}")
        }
        Outcome::Refused(why) => format!(
            "**Refused — nothing committed, no receipt.**\n> The executor refused the move: {why}"
        ),
    }
}

/// A verify report as an honest line.
pub fn verify_note(report: &VerifyReport) -> String {
    if report.verified {
        format!(
            "✓ **{} verified turns re-verify.** {}",
            report.turns, report.detail
        )
    } else {
        format!(
            "✗ **The chain does NOT re-verify** over {} turns:\n> {}",
            report.turns, report.detail
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The SYNC core of a press — what the tests drive and the async handlers wrap.
// ─────────────────────────────────────────────────────────────────────────────

/// The result of driving a component press through the offering.
///
/// (`Fired` is the big variant — it carries a real `TurnReceipt`. That is the payload, and a
/// `Driven` is built exactly once per press, so the size difference buys nothing to box away.)
#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Driven {
    /// The press resolved on the substrate — a real landed receipt or a real refusal.
    Fired(Outcome),
    /// The affordance takes a typed value: the frontend must open this modal.
    NeedsValue {
        /// The affordance verb whose value the modal collects.
        turn: String,
        /// The prompt to render.
        prompt: ValuePrompt,
    },
    /// No session of this offering is open in the channel.
    NoSession,
    /// The custom-id is not this offering's.
    NotOurs,
}

/// **Drive one component press.** Decodes the custom-id and, for a fixed-arg affordance, runs
/// ONE real [`Offering::advance`] attributed to `actor`. This is the whole logic of a live
/// button press; [`handle_component`] only adds the serenity round-trip.
pub fn drive<O: DiscordOffering>(channel: u64, custom_id: &str, actor: DreggIdentity) -> Driven {
    let press = match parse_press(custom_id) {
        Some(p) => p,
        None => return Driven::NotOurs,
    };
    match press {
        Press::Ask { key, turn } if key == O::KEY => match O::value_prompt(&turn) {
            Some(prompt) => Driven::NeedsValue { turn, prompt },
            // A value-less turn addressed as `ask` — fire it with arg 0 rather than dead-ending.
            None => drive_value::<O>(channel, &turn, 0, actor),
        },
        Press::Fire { key, turn, arg } if key == O::KEY => {
            drive_value::<O>(channel, &turn, arg, actor)
        }
        _ => Driven::NotOurs,
    }
}

/// **Drive an affordance with an explicit arg** — the modal-submit path (and the fixed-arg
/// path's own body). ONE real offering turn, attributed to the presser's dregg identity.
pub fn drive_value<O: DiscordOffering>(
    channel: u64,
    turn: &str,
    arg: i64,
    actor: DreggIdentity,
) -> Driven {
    // The action is resolved on the store's own thread (where the session lives), so it owns
    // its strings.
    let turn = turn.to_string();
    let outcome = with_live::<O, _>(channel, move |live| {
        // The label is decoration; the executor resolves the TYPED (turn, arg) — and `enabled`
        // is a decoration too (we pass `true`), because the substrate is the sole referee: a
        // move it does not admit comes back as a real `Refused`, not a frontend veto.
        let action = Action::new(turn.clone(), turn, arg, true);
        live.offering.advance(&mut live.session, action, actor)
    });
    match outcome {
        Some(o) => Driven::Fired(o),
        None => Driven::NoSession,
    }
}

/// Re-verify the channel's committed chain through [`Offering::verify`].
pub fn verify_live<O: DiscordOffering>(channel: u64) -> Option<VerifyReport> {
    with_live::<O, _>(channel, |live| live.offering.verify(&live.session))
}

// ─────────────────────────────────────────────────────────────────────────────
// The async Discord handlers — thin wrappers over the sync core.
// ─────────────────────────────────────────────────────────────────────────────

/// Post the channel's live surface (embed + affordance buttons) as the command response.
pub async fn handle_status<O: DiscordOffering>(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    let rendered = with_live::<O, _>(channel, |live| surface_of::<O>(live));
    match rendered {
        Some((embed, rows)) => {
            let msg = CreateInteractionResponseMessage::new()
                .embed(embed)
                .components(rows);
            let _ = command
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
        None => ephemeral(ctx, command, &no_session_text::<O>()).await,
    }
}

/// Re-verify the channel's chain and post the honest report.
pub async fn handle_verify<O: DiscordOffering>(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    match verify_live::<O>(channel) {
        Some(report) => {
            let embed = CreateEmbed::new()
                .title(format!("{} — verify", O::TITLE))
                .description(verify_note(&report))
                .color(if report.verified { O::COLOR } else { 0xE63946 });
            let msg = CreateInteractionResponseMessage::new().embed(embed);
            let _ = command
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
        None => ephemeral(ctx, command, &no_session_text::<O>()).await,
    }
}

/// Route a component press: fire it as a real turn (and re-render the surface with the outcome),
/// or open the modal a value-taking affordance needs.
pub async fn handle_component<O: DiscordOffering>(
    ctx: &Context,
    component: &ComponentInteraction,
    state: &BotState,
) {
    let channel = component.channel_id.get();
    let actor = identity_of(state, component.user.id.get());
    match drive::<O>(channel, &component.data.custom_id, actor) {
        Driven::NeedsValue { turn, prompt } => {
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Modal(value_modal::<O>(&turn, prompt)),
                )
                .await;
        }
        Driven::Fired(outcome) => {
            update_surface::<O>(ctx, component, channel, &outcome_note(&outcome)).await;
        }
        Driven::NoSession => {
            component_ephemeral(ctx, component, &no_session_text::<O>()).await;
        }
        Driven::NotOurs => {}
    }
}

/// Route a modal submit: parse the typed value and fire the affordance as a real turn.
pub async fn handle_modal<O: DiscordOffering>(
    ctx: &Context,
    modal: &ModalInteraction,
    state: &BotState,
) {
    let Some((key, turn)) = parse_submit(&modal.data.custom_id) else {
        return;
    };
    if key != O::KEY {
        return;
    }
    let raw = modal_value(modal, VALUE_FIELD);
    let Ok(value) = raw.trim().parse::<i64>() else {
        let _ = modal
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .content(format!("`{raw}` is not a whole number."))
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    };
    let channel = modal.channel_id.get();
    let actor = identity_of(state, modal.user.id.get());
    match drive_value::<O>(channel, &turn, value, actor) {
        Driven::Fired(outcome) => {
            let note = outcome_note(&outcome);
            let rendered = with_live::<O, _>(channel, |live| surface_of::<O>(live));
            let msg = match rendered {
                Some((embed, rows)) => CreateInteractionResponseMessage::new()
                    .content(note)
                    .embed(embed)
                    .components(rows),
                None => CreateInteractionResponseMessage::new().content(note),
            };
            let _ = modal
                .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
                .await;
        }
        _ => {
            let _ = modal
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(no_session_text::<O>())
                            .ephemeral(true),
                    ),
                )
                .await;
        }
    }
}

/// Re-render the channel's surface into the pressed message, with the move's honest outcome.
async fn update_surface<O: DiscordOffering>(
    ctx: &Context,
    component: &ComponentInteraction,
    channel: u64,
    note: &str,
) {
    let rendered = with_live::<O, _>(channel, |live| surface_of::<O>(live));
    let Some((embed, rows)) = rendered else {
        component_ephemeral(ctx, component, &no_session_text::<O>()).await;
        return;
    };
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::UpdateMessage(
                CreateInteractionResponseMessage::new()
                    .content(truncate(note, 1900))
                    .embed(embed)
                    .components(rows),
            ),
        )
        .await;
}

fn no_session_text<O: DiscordOffering>() -> String {
    format!(
        "No {} session is open in this channel. Start one with `/{} open`.",
        O::KEY,
        O::KEY
    )
}

async fn ephemeral(ctx: &Context, command: &CommandInteraction, text: &str) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(text)
                    .ephemeral(true),
            ),
        )
        .await;
}

async fn component_ephemeral(ctx: &Context, component: &ComponentInteraction, text: &str) {
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(text)
                    .ephemeral(true),
            ),
        )
        .await;
}

/// Read a modal text field by id.
fn modal_value(modal: &ModalInteraction, id: &str) -> String {
    for row in &modal.data.components {
        for component in &row.components {
            if let ActionRowComponent::InputText(input) = component
                && input.custom_id == id
            {
                return input.value.clone().unwrap_or_default();
            }
        }
    }
    String::new()
}

/// Truncate `s` to at most `max` characters (char-safe).
pub fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
    out.push('…');
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The routers — `main.rs` sends every `offering:` press/modal here; we dispatch on the key.
// ─────────────────────────────────────────────────────────────────────────────

/// Dispatch an `offering:` component press to the offering that owns the key.
pub async fn route_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let Some(key) = key_of(&component.data.custom_id) else {
        return;
    };
    match key.as_str() {
        k if k == <dreggnet_council::CouncilOffering as DiscordOffering>::KEY => {
            handle_component::<dreggnet_council::CouncilOffering>(ctx, component, state).await
        }
        k if k == <dreggnet_market::MarketOffering as DiscordOffering>::KEY => {
            handle_component::<dreggnet_market::MarketOffering>(ctx, component, state).await
        }
        _ => {}
    }
}

/// Dispatch an `offering:` modal submit to the offering that owns the key.
pub async fn route_modal(ctx: &Context, modal: &ModalInteraction, state: &BotState) {
    let Some(key) = key_of(&modal.data.custom_id) else {
        return;
    };
    match key.as_str() {
        k if k == <dreggnet_council::CouncilOffering as DiscordOffering>::KEY => {
            handle_modal::<dreggnet_council::CouncilOffering>(ctx, modal, state).await
        }
        k if k == <dreggnet_market::MarketOffering as DiscordOffering>::KEY => {
            handle_modal::<dreggnet_market::MarketOffering>(ctx, modal, state).await
        }
        _ => {}
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the wire codec + the rendering contract, driven with no live Discord.
// (The offering-driving tests live beside each offering: `commands::council`,
// `commands::market`.)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_custom_id_wire_round_trips() {
        let fire = fire_id("council", "approve", 2);
        assert_eq!(fire, "offering:fire:council:approve:2");
        assert_eq!(
            parse_press(&fire),
            Some(Press::Fire {
                key: "council".into(),
                turn: "approve".into(),
                arg: 2
            })
        );

        let ask = ask_id("market", "bid");
        assert_eq!(ask, "offering:ask:market:bid");
        assert_eq!(
            parse_press(&ask),
            Some(Press::Ask {
                key: "market".into(),
                turn: "bid".into()
            })
        );

        assert_eq!(
            parse_submit(&submit_id("market", "list")),
            Some(("market".into(), "list".into()))
        );

        assert_eq!(key_of(&fire).as_deref(), Some("council"));
        assert_eq!(key_of(&ask).as_deref(), Some("market"));
        assert_eq!(
            key_of(&submit_id("market", "list")).as_deref(),
            Some("market")
        );
    }

    /// A foreign custom-id (the `/dungeon` ballot, the ViewNode card route, the dashboard) is
    /// NOT ours — the router must ignore it rather than mis-fire a turn.
    #[test]
    fn a_foreign_custom_id_is_not_ours() {
        for id in [
            "fiction:vote:0:1",
            "deosturn:increment:1",
            "deos:abc12345:grant",
            "dregg:panel:identity",
            "start:menu",
            "offering:bogus:market:bid",
        ] {
            assert_eq!(parse_press(id), None, "{id} must not decode as a press");
            assert_eq!(parse_submit(id), None, "{id} must not decode as a submit");
        }
        assert_eq!(key_of("fiction:vote:0:1"), None);
    }

    #[test]
    fn an_outcome_is_reported_honestly() {
        let refused = Outcome::Refused("below quorum: the proposal has not passed".into());
        let note = outcome_note(&refused);
        assert!(note.contains("Refused"), "{note}");
        assert!(note.contains("nothing committed, no receipt"), "{note}");
        assert!(
            note.contains("below quorum"),
            "the executor's own reason survives: {note}"
        );
    }
}
