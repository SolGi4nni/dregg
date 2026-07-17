//! **The per-identity PERSISTENT RPG world** behind `/play trade|craft|inventory|guild|cheevos|
//! companion|tavern|party` — the fix for the audit's biggest depth failure (backlog #15, folding
//! in #24).
//!
//! Before this module those eight `/play` keys each opened a THROWAWAY demo world
//! (`SharedWorld::demo("Adventurer")`, `CheevoShowcase::demo()`): canned stock, forgotten on
//! restart, and — the deepest cut — **no composition**: trade, craft and inventory each stood on
//! their own private ledger, so a forged Greatblade was not in your inventory and not listable.
//!
//! This module mounts, for **each player's derived dregg identity**, one persistent
//! [`OfferingHost`] built by [`dreggnet_surfaces::register_surfaces`] — the SAME one-call
//! registration the web catalog uses, which mounts trade + craft + inventory onto **ONE
//! [`SharedWorld`](dreggnet_surfaces::SharedWorld)** (one `AssetWorld`, one item registry). So on
//! Discord, as on the web: forge a Greatblade on the craft surface and it IS in your inventory
//! and IS listable on your trade stall, as the same note-cell (the `dreggnet-saga` composition).
//!
//! ## Persistence — replay, never a state blob
//!
//! Each player's host writes through a [`SqliteRpgResumeStore`] (`rpg_store`, the durable sqlite
//! impl the core resume seam names as the bot's follow-up): every session open (its seed) and
//! every LANDED advance persists as reproducible public input. On the player's first touch after
//! a restart the host is rebuilt by REPLAYING those logs through the real executor
//! ([`OfferingHost::resume`]) — a tampered log is refused on re-drive and fails closed, never
//! reopened to a forged state.
//!
//! Because craft / inventory / trade share ONE world, the replay order across their per-session
//! logs matters (a crafted note must exist before its listing re-drives). [`order_logs_for_replay`]
//! replays **craft first** (the only surface that MINTS into the shared ledger), then the movers.
//! Residual (named): the exact cross-session interleaving is not recorded, so an exotic
//! interleave two lanes both touching one note in opposite order could re-drive to a refusal —
//! the session then honestly fails to reopen (its log is kept; nothing forged goes live).
//!
//! ## Real earned cheevos (#24)
//!
//! The `cheevos` key no longer shows `CheevoShowcase::demo()` (Ada's museum). At host build the
//! player's OWN persisted `/descent` board completions (the no-cheat store `descent_completions`)
//! are replayed and fed to [`CheevoLedger::earn`] — the full gate: re-execute the run against the
//! regenerated day-world, then hold the achievement predicate over the run's REAL committed
//! trajectory. A player who has cleared nothing sees an honest empty showcase; nothing is
//! inherited from a demo fixture.
//!
//! ## Identity semantics
//!
//! The world is **yours**: `/play craft` opens YOUR forge in any channel, and a button press on
//! any rendered surface acts in the PRESSER's own world (the embed re-renders as theirs). The
//! canned trade counterparty ("buyer" and its purse) is part of the seeded single-player world —
//! cross-player trading is a named next step, not faked here.

use std::collections::HashMap;
use std::sync::OnceLock;
use std::sync::mpsc::{SyncSender, sync_channel};

use serenity::all::{
    CommandInteraction, ComponentInteraction, Context, CreateActionRow, CreateEmbed,
    CreateEmbedFooter, EditInteractionResponse,
};

use dreggnet_cheevo::{Achievement, Cheevo, CheevoLedger};
use dreggnet_offerings::resume::{SessionMoveLog, SessionResumeStore};
use dreggnet_offerings::{Action, DreggIdentity, OfferingHost, SessionId};
use dreggnet_surfaces::{
    CheevoShowcase, CompanionOffering, CraftOffering, GuildPage, InventoryOffering, PartyOffering,
    TavernOffering, TradeOffering, register_surfaces,
};
use ugc_dregg::{Completion, Universe, record_playthrough};

use crate::BotState;
use crate::commands::ack;
use crate::commands::descent::{
    StoredDescentCompletion, StoredDescentUniverse, reconstruct_universe,
};
use crate::commands::offering::{
    self, DiscordOffering, Press, identity_of, outcome_note, truncate,
};
use crate::db::Database;
use crate::rpg_store::SqliteRpgResumeStore;

/// The eight `/play` keys this module serves out of the per-identity persistent host (the other
/// four `/play` keys — the games + names/compute — keep their per-channel generic-adapter stores).
pub const RPG_KEYS: [&str; 8] = [
    "trade",
    "inventory",
    "cheevos",
    "guild",
    "craft",
    "companion",
    "tavern",
    "party",
];

/// Whether `key` is one of the eight RPG-world keys this module owns.
pub fn is_rpg_key(key: &str) -> bool {
    RPG_KEYS.contains(&key)
}

/// The one session slot each RPG surface occupies in a player's host. A player's inventory is a
/// singleton (per identity, not per channel) — `/play inventory` anywhere is the same world.
const SESSION: &str = "primary";

fn session_id() -> SessionId {
    SessionId::new(SESSION)
}

/// The per-key embed identity — the SAME `TITLE`/`COLOR`/`TAGLINE` the generic adapter's
/// `DiscordOffering` impls (`commands::portfolio`) declare, so the persistent surface renders
/// byte-consistent with the rest of the offering family.
fn meta(key: &str) -> Option<(&'static str, u32, &'static str)> {
    macro_rules! m {
        ($ty:ty) => {
            Some((
                <$ty as DiscordOffering>::TITLE,
                <$ty as DiscordOffering>::COLOR,
                <$ty as DiscordOffering>::TAGLINE,
            ))
        };
    }
    match key {
        "trade" => m!(TradeOffering),
        "inventory" => m!(InventoryOffering),
        "cheevos" => m!(CheevoShowcase),
        "guild" => m!(GuildPage),
        "craft" => m!(CraftOffering),
        "companion" => m!(CompanionOffering),
        "tavern" => m!(TavernOffering),
        "party" => m!(PartyOffering),
        _ => None,
    }
}

/// The affordance rows for `key`'s current actions — through the generic adapter's own
/// [`offering::action_rows`] (same custom-id wire, same 🔒-shown-not-hidden styling), so a press
/// on a persistent surface routes exactly like every other offering press.
fn rows_for(key: &str, actions: &[Action]) -> Vec<CreateActionRow> {
    match key {
        "trade" => offering::action_rows::<TradeOffering>(actions),
        "inventory" => offering::action_rows::<InventoryOffering>(actions),
        "cheevos" => offering::action_rows::<CheevoShowcase>(actions),
        "guild" => offering::action_rows::<GuildPage>(actions),
        "craft" => offering::action_rows::<CraftOffering>(actions),
        "companion" => offering::action_rows::<CompanionOffering>(actions),
        "tavern" => offering::action_rows::<TavernOffering>(actions),
        "party" => offering::action_rows::<PartyOffering>(actions),
        _ => Vec::new(),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Building one player's persistent host (pure over an injected store — tested).
// ─────────────────────────────────────────────────────────────────────────────

/// Replay priority of an offering key. **Craft replays first**: it is the only surface that MINTS
/// into the shared ledger, so every note a later inventory-gift / trade-list re-drives against
/// already exists. Companion mints too (into its own roost — order-independent, kept early for
/// symmetry); the pure read-surfaces replay last.
fn replay_rank(key: &str) -> usize {
    match key {
        "craft" => 0,
        "companion" => 1,
        "inventory" => 2,
        "trade" => 3,
        "guild" => 4,
        "party" => 5,
        _ => 6,
    }
}

/// Order a player's persisted session logs for replay (see [`replay_rank`]); deterministic
/// (rank, key, id) so a rebuild is reproducible.
pub fn order_logs_for_replay(mut logs: Vec<SessionMoveLog>) -> Vec<SessionMoveLog> {
    logs.sort_by(|a, b| {
        (replay_rank(&a.key), &a.key, &a.id.0).cmp(&(replay_rank(&b.key), &b.key, &b.id.0))
    });
    logs
}

/// **Build one player's persistent RPG host**: mount the eight surfaces via the web-parity
/// [`register_surfaces`] (ONE shared world across craft/inventory/trade), replace the demo
/// cheevo showcase with the player's REAL earned cheevos, attach the durable store, and reopen
/// every persisted session by replay (craft-first ordering). A log that refuses to re-drive is
/// reported and left closed — fail-closed, its durable record kept.
pub fn build_player_host(store: Box<dyn SessionResumeStore>, cheevos: Vec<Cheevo>) -> OfferingHost {
    let logs = order_logs_for_replay(store.all());
    let mut host = OfferingHost::new().with_resume_store(store);
    register_surfaces(&mut host);
    // #24 — the player's OWN earned proofs, not Ada's demo museum. Re-registering the key
    // replaces the demo showcase `register_surfaces` mounted.
    host.register(
        "cheevos",
        "Achievements — earned soulbound proofs over verified runs",
        CheevoShowcase::from_cheevos(cheevos),
    );
    for log in logs {
        if let Err(e) = host.resume(&log) {
            tracing::warn!(
                key = %log.key,
                session = %log.id.0,
                "a persisted RPG session refused to reopen (kept closed, log retained): {e}"
            );
        }
    }
    host
}

// ─────────────────────────────────────────────────────────────────────────────
// #24 — real earned cheevos over the player's own persisted completions.
// ─────────────────────────────────────────────────────────────────────────────

/// The achievement ladder tried against each verified completion, strongest-first per category —
/// the FIRST predicate in a category that genuinely holds over the run's committed trajectory is
/// the one earned (so a depth-8 clear shows "Deep Delver (≥8)", not three nested badges).
fn achievement_ladders() -> Vec<Vec<Achievement>> {
    let depth = |min: u64| Achievement::ReachedDepth {
        var: "depth".to_string(),
        min,
    };
    vec![
        vec![depth(8), depth(5), depth(3)],
        vec![
            Achievement::SpeedClear { max_turns: 4 },
            Achievement::SpeedClear { max_turns: 6 },
            Achievement::SpeedClear { max_turns: 10 },
        ],
    ]
}

/// **Earn the player's real cheevos** from their persisted `/descent` board completions. Pure
/// over its inputs (tested without a database): for each completion by `player_tag`, the run is
/// re-recorded against its regenerated day-world and fed to [`CheevoLedger::earn`] — the full
/// no-cheat gate + the anchored predicate. A row that fails to re-drive earns nothing (dropped,
/// exactly as the board's own boot replay drops it). De-duplicated per achievement across runs.
pub fn earn_player_cheevos(
    player_tag: &str,
    universes: &[(String, Universe)],
    completions: &[StoredDescentCompletion],
) -> Vec<Cheevo> {
    let mut ledger = CheevoLedger::new();
    let mut earned: Vec<Cheevo> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    for sc in completions.iter().filter(|c| c.player == player_tag) {
        let Some((_, universe)) = universes.iter().find(|(id, _)| *id == sc.universe_id_hex) else {
            continue;
        };
        let Ok(moves) = serde_json::from_str::<Vec<usize>>(&sc.moves_json) else {
            continue;
        };
        // A tampered (illegal) move sequence is refused by the real executor here.
        let Ok(play) = record_playthrough(universe, &moves) else {
            continue;
        };
        let completion = Completion {
            universe: universe.id(),
            player: sc.player.clone(),
            play,
            claimed_turns: sc.claimed_turns as usize,
        };
        for ladder in achievement_ladders() {
            for achievement in ladder {
                if let Ok(c) = ledger.earn(universe, &completion, achievement) {
                    if seen.insert(format!("{:?}", c.achievement)) {
                        earned.push(c);
                    }
                    break; // strongest-in-category earned; skip the weaker rungs
                }
            }
        }
    }
    earned
}

/// The db-wired assembly of [`earn_player_cheevos`]: load the persisted day-universes
/// (regenerated from their committed seeds, tamper-checked) and the player's completions off the
/// SAME durable no-cheat store `/descent` writes. `player_tag` matching uses the first-12-hex tag
/// the board persists (`descent.rs`'s `short_player`).
fn cheevos_for(db: &Database, handle: &tokio::runtime::Handle, player_hex: &str) -> Vec<Cheevo> {
    let universes: Vec<(String, Universe)> = block_on(handle, db.list_descent_universes())
        .unwrap_or_default()
        .into_iter()
        .filter_map(|r| {
            let su = StoredDescentUniverse {
                id_hex: r.id_hex.clone(),
                author: r.author,
                seed_hex: r.seed_hex,
            };
            reconstruct_universe(&su).map(|u| (r.id_hex, u))
        })
        .collect();
    let completions: Vec<StoredDescentCompletion> = block_on(handle, db.list_descent_completions())
        .unwrap_or_default()
        .into_iter()
        .map(|r| StoredDescentCompletion {
            key_hex: r.key_hex,
            universe_id_hex: r.universe_id_hex,
            player: r.player,
            moves_json: r.moves_json,
            claimed_turns: r.claimed_turns,
        })
        .collect();
    let tag: String = player_hex.chars().take(12).collect();
    earn_player_cheevos(&tag, &universes, &completions)
}

/// Drive an async DB future to completion synchronously — the sync↔async bridge, identical to
/// `rpg_store::SqliteRpgResumeStore::block` (the host thread is a non-tokio `std::thread`, so the
/// stored handle is the norm; inside a runtime worker the current handle is used).
fn block_on<F: std::future::Future>(handle: &tokio::runtime::Handle, fut: F) -> F::Output {
    match tokio::runtime::Handle::try_current() {
        Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
        Err(_) => handle.block_on(fut),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The host seam — one dedicated thread OWNS every player's host (an OfferingHost
// is !Send: the shared world is Rc-backed; the same confinement shape as the
// generic adapter's per-offering `Store`).
// ─────────────────────────────────────────────────────────────────────────────

type HostMap = HashMap<String, OfferingHost>;
type HostJob = Box<dyn FnOnce(&mut HostMap) + Send + 'static>;

struct HostSeam {
    jobs: SyncSender<HostJob>,
}

static HOSTS: OnceLock<HostSeam> = OnceLock::new();

fn seam() -> &'static HostSeam {
    HOSTS.get_or_init(|| {
        let (jobs, rx) = sync_channel::<HostJob>(64);
        std::thread::Builder::new()
            .name("rpg-worlds".to_string())
            .spawn(move || {
                let mut hosts: HostMap = HashMap::new();
                while let Ok(job) = rx.recv() {
                    job(&mut hosts);
                }
            })
            .expect("spawn the rpg-worlds host thread");
        HostSeam { jobs }
    })
}

/// Run `f` against the host map on the owning thread and hand back its result.
fn run<R: Send + 'static>(f: impl FnOnce(&mut HostMap) -> R + Send + 'static) -> R {
    let (tx, rx) = sync_channel::<R>(1);
    seam()
        .jobs
        .send(Box::new(move |hosts| {
            let _ = tx.send(f(hosts));
        }))
        .expect("the rpg-worlds host thread is alive");
    rx.recv().expect("the rpg-worlds host thread answered")
}

/// Run `f` against `player`'s host, building it first if this is the player's first touch since
/// boot (register + real cheevos + full replay of their persisted sessions — the durable store is
/// scoped to the player, so no other identity's rows are ever read).
fn with_player_host<R: Send + 'static>(
    db: Database,
    handle: tokio::runtime::Handle,
    player: String,
    f: impl FnOnce(&mut OfferingHost, &DreggIdentity) -> R + Send + 'static,
) -> R {
    run(move |hosts| {
        let viewer = DreggIdentity(player.clone());
        let host = hosts.entry(player.clone()).or_insert_with(|| {
            let cheevos = cheevos_for(&db, &handle, &player);
            let store = SqliteRpgResumeStore::new(db.clone(), handle.clone(), player.clone());
            build_player_host(Box::new(store), cheevos)
        });
        f(host, &viewer)
    })
}

/// TEST/OPS HOOK: drop a player's in-memory host (their durable logs stay; the next touch
/// rebuilds by replay — the same path a process restart takes).
#[allow(dead_code)]
pub fn evict_player_host(player: &str) {
    let player = player.to_string();
    run(move |hosts| {
        hosts.remove(&player);
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// The sync render/press core (host-thread side; only plain data crosses back).
// ─────────────────────────────────────────────────────────────────────────────

/// Render `key`'s live surface out of `host`, projected FOR `viewer` — embed + affordance rows,
/// in the same visual grammar as the generic adapter (`embed_for`/`action_rows`), with the honest
/// persistent-world footer.
fn surface_from_host(
    host: &OfferingHost,
    key: &str,
    viewer: &DreggIdentity,
) -> Option<(CreateEmbed, Vec<CreateActionRow>)> {
    let id = session_id();
    let surface = host.render_for(key, &id, viewer)?;
    let actions = host.actions_for(key, &id, viewer).unwrap_or_default();
    let turns = host.verify(key, &id).map(|r| r.turns).unwrap_or(0);
    let (title, color, tagline) = meta(key)?;
    let card = deos_view::discord::render_card(title, surface.view(), &[]);
    let embed = card
        .embed
        .color(color)
        .footer(CreateEmbedFooter::new(truncate(
            &format!("{turns} verified turns · {tagline} · your own world — it persists"),
            2040,
        )));
    Some((embed, rows_for(key, &actions)))
}

/// The `Send` result of an open or press against a player's persistent world.
pub struct RpgSurface {
    /// The honest note (a landed receipt's `turn_hash`, the executor's refusal, or an open error).
    pub note: String,
    /// The re-rendered surface, if the session is live.
    pub surface: Option<(CreateEmbed, Vec<CreateActionRow>)>,
}

/// **Open (or touch) `key` in `player`'s persistent world and render it.** First touch since boot
/// rebuilds the host by replay; a fresh key mints its one persistent session.
fn open_core(
    db: Database,
    handle: tokio::runtime::Handle,
    player: String,
    key: String,
) -> RpgSurface {
    with_player_host(db, handle, player, move |host, viewer| {
        let id = session_id();
        if let Err(e) = host.ensure_open(&key, &id) {
            return RpgSurface {
                note: format!(
                    "**The offering was not opened.** {e}\n> Nothing was reset — the persisted \
                     record is kept; this surface fails closed rather than reopening a world \
                     that does not re-verify."
                ),
                surface: None,
            };
        }
        RpgSurface {
            note: String::new(),
            surface: surface_from_host(host, &key, viewer),
        }
    })
}

/// **Drive one press as one real turn in the PRESSER's own world** (ensure-open first, so a
/// button on a pre-restart message transparently resumes their world), then re-render.
fn press_core(
    db: Database,
    handle: tokio::runtime::Handle,
    player: String,
    key: String,
    turn: String,
    arg: i64,
) -> RpgSurface {
    with_player_host(db, handle, player, move |host, viewer| {
        let id = session_id();
        if let Err(e) = host.ensure_open(&key, &id) {
            return RpgSurface {
                note: format!("**The world did not reopen.** {e}"),
                surface: None,
            };
        }
        // The label is decoration; the executor resolves the TYPED (turn, arg) — `enabled` is
        // decoration too (the substrate is the sole referee; an inadmissible move comes back as
        // a real `Refused`, not a frontend veto).
        let action = Action::new(turn.clone(), turn, arg, true);
        let note = match host.advance(&key, &id, action, viewer.clone()) {
            Some(outcome) => outcome_note(&outcome),
            None => "No live session — the world did not reopen.".to_string(),
        };
        RpgSurface {
            note,
            surface: surface_from_host(host, &key, viewer),
        }
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// The async Discord handlers — thin wrappers (defer-first: a first-touch replay
// of a long history may exceed Discord's 3s window).
// ─────────────────────────────────────────────────────────────────────────────

/// Route `/play <rpg-key>` — open the key in the invoker's persistent world and post its surface.
/// Called by `commands::portfolio::handle` for every [`is_rpg_key`] key, AFTER that handler's
/// `defer_slash` (the caller owns the 3s ACK; this function only edits the deferred response —
/// a first-touch replay of a long history may exceed the window, which is exactly why).
pub async fn handle_play(ctx: &Context, command: &CommandInteraction, state: &BotState, key: &str) {
    let db = state.db.clone();
    let handle = tokio::runtime::Handle::current();
    let player = identity_of(state, command.user.id.get()).0;
    let opened = open_core(db, handle, player, key.to_string());
    match opened.surface {
        Some((embed, rows)) => ack::edit_slash(ctx, command, embed, rows).await,
        None => {
            let embed = CreateEmbed::new()
                .title("The offering was not opened")
                .description(truncate(&opened.note, 4000))
                .color(0xE63946);
            ack::edit_slash(ctx, command, embed, Vec::new()).await;
        }
    }
}

/// Route an `offering:` component press whose key is an RPG-world key: one real turn in the
/// PRESSER's own persistent world, then the pressed message re-renders as their projection.
/// Wired from `commands::offering::route_component`.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let Some(press) = offering::parse_press(&component.data.custom_id) else {
        return;
    };
    // The eight RPG surfaces declare no value/text prompts, so every press is a direct fire
    // (an `ask`-shaped id would only arise from a stale foreign message — fire it honestly
    // with its arg rather than dead-ending, the same fallback `offering::drive` takes).
    let (key, turn, arg) = match press {
        Press::Fire { key, turn, arg } => (key, turn, arg),
        Press::Ask { key, turn } => (key, turn, 0),
        Press::AskText { key, turn, arg } => (key, turn, arg),
    };
    if !is_rpg_key(&key) {
        return;
    }
    ack::ack_component(ctx, component).await;
    let db = state.db.clone();
    let handle = tokio::runtime::Handle::current();
    let player = identity_of(state, component.user.id.get()).0;
    let pressed = press_core(db, handle, player, key, turn, arg);
    match pressed.surface {
        Some((embed, rows)) => {
            let _ = component
                .edit_response(
                    &ctx.http,
                    EditInteractionResponse::new()
                        .content(truncate(&pressed.note, 1900))
                        .embed(embed)
                        .components(rows),
                )
                .await;
        }
        None => ack::followup_ephemeral(ctx, component, &truncate(&pressed.note, 1900)).await,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the composition, the persistence-by-replay, the identity isolation,
// and the real-cheevo gate, all driven at the logic level over the injected
// store (no Discord, no sqlite).
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::Surface;
    use dreggnet_offerings::resume::InMemoryResumeStore;
    use ugc_dregg::WinCondition;

    fn me() -> DreggIdentity {
        DreggIdentity(format!("aa{}", "0".repeat(62)))
    }

    fn view_text(surface: &Surface) -> String {
        format!("{:?}", surface.view())
    }

    fn render_text(host: &OfferingHost, key: &str, viewer: &DreggIdentity) -> String {
        view_text(
            &host
                .render_for(key, &session_id(), viewer)
                .unwrap_or_else(|| panic!("`{key}` renders")),
        )
    }

    /// Craft the bench's recipe 0 (Greatblade — a SAFE recipe: its odds sit wholly on success)
    /// as one real landed turn.
    fn craft_greatblade(host: &mut OfferingHost, who: &DreggIdentity) {
        let id = session_id();
        host.ensure_open("craft", &id).expect("craft opens");
        let out = host
            .advance(
                "craft",
                &id,
                Action::new("Forge Greatblade", "craft", 0, true),
                who.clone(),
            )
            .expect("craft session live");
        assert!(out.landed(), "the greatblade craft lands: {out:?}");
    }

    /// **THE SAGA COMPOSITION (#15's heart)** — a crafted item IS in the player's inventory IS
    /// tradeable, because the three surfaces stand on ONE shared world (`register_surfaces`),
    /// not three per-open demo look-alikes.
    #[test]
    fn a_crafted_item_is_in_the_inventory_and_tradeable() {
        let mut host = build_player_host(Box::new(InMemoryResumeStore::new()), Vec::new());
        let who = me();
        let id = session_id();
        host.ensure_open("inventory", &id).expect("inventory opens");
        host.ensure_open("trade", &id).expect("trade opens");

        // Before the craft: no Greatblade anywhere (it is not seeded — only forged).
        assert!(!render_text(&host, "inventory", &who).contains("Greatblade"));

        craft_greatblade(&mut host, &who);

        // The SAME note-cell reaches the inventory read…
        assert!(
            render_text(&host, "inventory", &who).contains("Greatblade"),
            "the forged Greatblade is in the player's inventory (one ledger, no re-mint)"
        );
        // …and the trade surface offers to LIST it (enabled — the player provably holds it).
        let actions = host
            .actions_for("trade", &id, &who)
            .expect("trade session live");
        assert!(
            actions
                .iter()
                .any(|a| a.turn == "list" && a.label.contains("Greatblade") && a.enabled),
            "the forged Greatblade is listable on the trade stall: {actions:?}"
        );
    }

    /// **PERSISTENCE BY REPLAY** — a world survives a "restart" (a fresh host over the same
    /// durable store): the crafted item and its live trade listing reopen to the identical
    /// committed state, craft-log-first so the listing re-drives against an existing note.
    #[test]
    fn the_world_survives_a_restart_by_replay() {
        let store = InMemoryResumeStore::new();
        let who = me();
        let id = session_id();
        {
            let mut host = build_player_host(Box::new(store.clone()), Vec::new());
            craft_greatblade(&mut host, &who);
            host.ensure_open("trade", &id).expect("trade opens");
            let list = host
                .actions_for("trade", &id, &who)
                .expect("live")
                .into_iter()
                .find(|a| a.turn == "list" && a.label.contains("Greatblade"))
                .expect("the crafted item is listable");
            let out = host
                .advance("trade", &id, list, who.clone())
                .expect("trade live");
            assert!(out.landed(), "the listing lands: {out:?}");
        }

        // "Restart": a brand-new host, same durable store — everything reopens by replay.
        let host = build_player_host(Box::new(store.clone()), Vec::new());
        assert!(host.is_open("craft", &session_id()), "craft resumed");
        assert!(host.is_open("trade", &session_id()), "trade resumed");
        assert!(
            host.verify("craft", &session_id()).expect("live").verified,
            "the resumed craft chain re-verifies"
        );
        let trade = render_text(&host, "trade", &who);
        assert!(
            trade.contains("Greatblade"),
            "the crafted + listed Greatblade survived the restart: {trade}"
        );
        // The inventory was never opened pre-restart; a fresh open still reads the REPLAYED
        // shared world (one ledger), so the crafted note is simply there.
        let mut host = host;
        host.ensure_open("inventory", &session_id())
            .expect("inventory opens over the replayed world");
        assert!(render_text(&host, "inventory", &who).contains("Greatblade"));
    }

    /// **PER-IDENTITY ISOLATION** — two players' worlds are disjoint objects: a craft in one
    /// never appears in the other.
    #[test]
    fn two_identities_have_disjoint_worlds() {
        let mut alice = build_player_host(Box::new(InMemoryResumeStore::new()), Vec::new());
        let mut bob = build_player_host(Box::new(InMemoryResumeStore::new()), Vec::new());
        let a = me();
        let b = DreggIdentity(format!("bb{}", "0".repeat(62)));
        craft_greatblade(&mut alice, &a);
        bob.ensure_open("inventory", &session_id())
            .expect("bob's inventory opens");
        assert!(
            !render_text(&bob, "inventory", &b).contains("Greatblade"),
            "bob's world holds no note alice forged"
        );
    }

    /// **#24's falsifier** — the cheevo surface shows the PLAYER's earned proofs, not the demo:
    /// a player who has cleared nothing sees an honest empty showcase (no "Ada", no canned rows).
    #[test]
    fn cheevos_are_the_players_own_not_the_demo() {
        let mut host = build_player_host(Box::new(InMemoryResumeStore::new()), Vec::new());
        host.ensure_open("cheevos", &session_id())
            .expect("cheevos opens");
        let text = render_text(&host, "cheevos", &me());
        assert!(
            text.contains("No achievements earned yet"),
            "an empty record renders the honest empty state: {text}"
        );
        assert!(
            !text.contains("Ada"),
            "the demo fixture's earner never leaks into a player's showcase: {text}"
        );
    }

    /// A tiny authored descent world (depth counter + a gold-seizing win) — the same shape the
    /// live day-worlds and `dreggnet-cheevo`'s own tests drive.
    const TRIAL: &str = r#"---
id: rpg-world-cheevo-trial
title: RPG World Cheevo Trial
weight: 1
---

=== mouth

A shaft plunges down.

* [Descend]
  ~ depth += 1
  -> deep1

=== deep1

Deeper.

* [Descend]
  ~ depth += 1
  -> deep2

=== deep2

Deeper still.

* [Descend]
  ~ depth += 1
  -> vault

=== vault

A relic gleams.

* [Seize it]
  ~ gold += 500
  -> END
"#;

    /// **Real earned cheevos over persisted completions** — the full `CheevoLedger::earn` gate
    /// runs (no-cheat replay + the anchored predicate over the real trajectory): the player's own
    /// winning run earns the depth + speed proofs (strongest rung per category, seals intact);
    /// a different player tag earns nothing off it; a tampered move line earns nothing.
    #[test]
    fn earn_player_cheevos_runs_the_real_gate() {
        let universe = Universe::authored(
            "RPG World Cheevo Trial",
            "rpg-world-cheevo",
            TRIAL,
            WinCondition::ended_with(&[("gold", 500)]),
        )
        .expect("the trial world authors");
        let id_hex: String = universe
            .id()
            .as_bytes()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let tag = "abcdef123456";
        let good = StoredDescentCompletion {
            key_hex: "k1".into(),
            universe_id_hex: id_hex.clone(),
            player: tag.into(),
            moves_json: "[0,0,0,0]".into(),
            claimed_turns: 4,
        };
        // A tampered row: an out-of-range move index the executor refuses on re-drive.
        let tampered = StoredDescentCompletion {
            key_hex: "k2".into(),
            universe_id_hex: id_hex.clone(),
            player: tag.into(),
            moves_json: "[9,9]".into(),
            claimed_turns: 2,
        };
        let universes = vec![(id_hex, universe)];

        let earned = earn_player_cheevos(tag, &universes, &[good.clone(), tampered]);
        assert!(
            earned
                .iter()
                .any(|c| matches!(&c.achievement, Achievement::ReachedDepth { min: 3, .. })),
            "the run really peaked at depth 3 — the depth proof is earned: {earned:?}"
        );
        assert!(
            earned
                .iter()
                .any(|c| matches!(&c.achievement, Achievement::SpeedClear { max_turns: 4 })),
            "won in 4 turns — the strongest speed rung is earned: {earned:?}"
        );
        assert!(
            earned.iter().all(|c| c.seal_intact()),
            "every earned cheevo's soulbound seal re-derives"
        );
        assert!(
            earned.iter().all(|c| c.player == tag),
            "every cheevo is bound to its earner"
        );

        // Someone else's tag earns nothing off this record.
        assert!(
            earn_player_cheevos("999999999999", &universes, &[good]).is_empty(),
            "another identity earns nothing from this player's completions"
        );
    }

    /// The replay ordering: craft logs re-drive FIRST (the minting surface), so a trade/inventory
    /// move over a crafted note never replays before the note exists.
    #[test]
    fn order_logs_for_replay_puts_the_minting_surface_first() {
        use dreggnet_offerings::SessionConfig;
        let log = |key: &str| SessionMoveLog::new(key, session_id(), SessionConfig::default());
        let ordered = order_logs_for_replay(vec![
            log("trade"),
            log("tavern"),
            log("inventory"),
            log("craft"),
        ]);
        let keys: Vec<&str> = ordered.iter().map(|l| l.key.as_str()).collect();
        assert_eq!(keys, vec!["craft", "inventory", "trade", "tavern"]);
    }
}
