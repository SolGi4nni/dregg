//! # `dreggnet-catalog` — the ONE statement of what the DreggNet offering catalog is.
//!
//! [`build_full_catalog`] registers the full 23-offering portfolio — the nine games
//! (native Descent · Descent campaign · dungeon · council · market · Dark Bazaar · multiway-tug · automatafl · private raid), the nine do-once RPG
//! feature surfaces ([`dreggnet_surfaces::register_surfaces`]: trade · inventory · cheevos ·
//! guild · craft · companion · quest · tavern · party), and the five service offerings (doc · names ·
//! compute · grain · hermes) — into a caller-supplied [`OfferingHost`]. Every frontend builds its
//! host through this one function, so "which offerings exist" stops being four hand-maintained
//! lists (`dreggnet_web::catalog_default_host` + `register_non_game_offerings`,
//! `dreggnet_telegram::host::telegram_default_host`, `dreggnet_wechat::host::wechat_default_host`,
//! and discord-bot's bespoke per-type stores) that can silently disagree.
//!
//! ## ⚑ What EXISTS vs. what we ADVERTISE
//!
//! Two different lists, deliberately:
//!
//! - [`CATALOG_KEYS`] — the 23 offerings that EXIST. All mounted, all routable, all openable by
//!   key or URL on every frontend. This is the parity contract.
//! - [`SHIPPED_KEYS`] — **the SHIP LIST**: the small curated set we put in front of a stranger.
//!   [`build_full_catalog`] stamps it onto the host ([`apply_ship_list`]), so every shelf that
//!   paints `OfferingHost::list_advertised_offerings` — the web catalog page, the Telegram
//!   `/offerings` and `/play` menus, the WeChat menu, the Mini App, the Discord Activity —
//!   inherits it with no per-frontend filter. The discord-bot builds no host, so it reads
//!   [`is_shipped`] in its `/play` choice list instead.
//!
//! **Unlisted is not deleted.** Nothing in the ship list gates opening, playing or verifying —
//! `every_unshipped_offering_still_opens_and_verifies_by_key` in this module's tests is the guard.
//! To re-list something, add its key to [`SHIPPED_KEYS`]. That is the whole change.
//!
//! ## What stays OUT of this crate
//! Everything platform-specific. A frontend derives its users' identities with its own
//! cipherclerk (`(bot_secret, platform_uid, federation_id)` → Ed25519 pubkey) and hands this
//! crate only plain `Send` data: the council electorate as raw pubkeys in [`CatalogConfig`].
//! The host is built on whatever thread the frontend's `HostThread::spawn` closure runs, so
//! the `!Send`-session confinement discipline (`dreggnet-web/src/lib.rs` `HostThread`,
//! `dreggnet-telegram/src/host.rs` `HostThread`) is unchanged — this crate never spawns a
//! thread and never holds a session.
//!
//! ## Shared tables vs. per-player worlds
//!
//! [`build_full_catalog`] builds ONE host: right for the shared tables (a council, a market, a
//! tug board, or party — several identities acting on one object), and WRONG for the eight
//! identity-owned RPG feature surfaces. Mounted globally those eight give every viewer the SAME
//! inventory (one `SharedWorld::demo("Adventurer")`, one ledger, one shelf label). [`PlayerWorlds`]
//! is the per-identity half: one [`OfferingHost`] per derived identity, each with its own world,
//! built and boot-resumed on first touch. A frontend routes [`is_rpg_key`] keys there and
//! everything else — including `party` — to its catalog host.
//!
//! ## State (Phase A + B-for-Telegram of docs/BOT-SHARED-BACKEND-DESIGN.md)
//! The registrars are complete ports of the (byte-identical) web/telegram registrations, and the
//! [`seated`] adapter is the complete port of `dreggnet-web/src/seated.rs` (the source of the four
//! byte-peers). `dreggnet-telegram` builds its host through [`full_catalog_host`] and re-exports
//! [`seated::SeatedTug`]; web now delegates too, while WeChat delegation and Discord's cutover onto
//! `OfferingHost` are the design doc's remaining Phases B and C.

use dreggnet_offerings::OfferingHost;
use dreggnet_offerings::campaign::DescentCampaignOffering;
use dreggnet_offerings::dungeon::DungeonOffering;
use dreggnet_offerings::native_descent::NativeDescentOffering;

use std::sync::{Mutex, OnceLock};

use dregg_automatafl::AutomataflOffering;
use dreggnet_council::{CandidateProposal, CouncilOffering};
use dreggnet_market::{DarkBazaarOffering, MarketOffering};
use dreggnet_surfaces::private_raid::HostedProofAssignedRaidOffering;
/// The day binding a live catalog carries, re-exported so a frontend can publish a day
/// ([`publish_todays_descent_day`]) without its own direct dependency on the beacon layer.
pub use procgen_dregg::CommittedSeed;
pub use procgen_dregg::beacon::{
    BeaconSource, DRAND_API_BASE, DailyBeacon, FetchError, HttpRoundFetch, VerifyError,
};

pub mod game_epoch;
pub mod game_publication;
pub mod game_spine;
pub mod player_worlds;
#[cfg(feature = "private-bazaar-live")]
pub mod private_bazaar_ingress;
#[cfg(feature = "private-bazaar-live")]
pub mod private_bazaar_live;
#[cfg(feature = "private-bazaar-live")]
pub mod private_bazaar_service;
#[cfg(feature = "private-bazaar-live")]
pub mod private_bazaar_targets;
#[cfg(feature = "private-bazaar-live")]
pub mod private_bazaar_worker;
#[cfg(feature = "private-fhegg-game-consequence")]
pub mod private_fhegg_game_consequence;
pub mod seated;
#[cfg(feature = "private-fhegg-game-consequence")]
pub mod shielded_crown_orchestration;
#[cfg(feature = "private-fhegg-game-consequence")]
pub mod shielded_dungeon_publication;

pub use game_epoch::{GameAuthorizationPhase, GameEpochError, GameEpochLedger};
pub use game_publication::{
    GamePublicationError, MAX_PUBLIC_GAME_FIELD_VALUE_BYTES, MAX_PUBLIC_GAME_FIELDS,
    PublicGameAttribution, PublicGameField, PublicGameFieldValue, PublicGameReceipt,
    PublicGameReceiptResult, project_public_game_receipt,
};
pub use game_spine::{
    BoundGameTurnExecution, GameActionRef, GameAffordance, GameArtifact, GameArtifactRef,
    GameAudience, GameCommand, GameHostIncarnation, GameKind, GameOperationRef, GameReceipt,
    GameResult, GameSessionBinding, GameSessionRef, GameSessionView, GameSpineError,
    SignedGameAction, execute_asserted_game_command, execute_bound_asserted_game_command,
    execute_bound_asserted_game_turn, execute_bound_signed_game_turn,
    execute_bound_signed_game_turn_with_outcome, execute_signed_game_turn,
    game_action_signing_message, game_kind, inspect_bound_game_session, inspect_game_session,
    sign_game_action, verify_signed_game_action,
};
pub use player_worlds::{PlayerWorlds, RPG_KEYS, build_player_host, is_rpg_key};
#[cfg(feature = "private-bazaar-live")]
pub use private_bazaar_ingress::{
    PrivateBazaarIngressError, PrivateBazaarIngressProgress, PrivateBazaarIngressSubmission,
    PrivateBazaarSealedIngressQueue,
};
#[cfg(feature = "private-bazaar-live")]
pub use private_bazaar_live::{
    PRIVATE_BAZAAR_RAID_TITLE, PrivateBazaarLiveDeployment, build_full_catalog_with_private_bazaar,
    full_catalog_host_with_private_bazaar,
};
#[cfg(feature = "private-bazaar-live")]
pub use private_bazaar_service::{
    PRIVATE_BAZAAR_WORKER_INITIAL_BACKOFF_MS_ENV, PRIVATE_BAZAAR_WORKER_MAX_BACKOFF_MS_ENV,
    PRIVATE_BAZAAR_WORKER_POLL_MS_ENV, PrivateBazaarAuthenticatedReceiptSource,
    PrivateBazaarLiveRuntime, PrivateBazaarSourceCapture, PrivateBazaarWorkerFaultClass,
    PrivateBazaarWorkerHealth, PrivateBazaarWorkerServiceConfig, PrivateBazaarWorkerServiceError,
    PrivateBazaarWorkerServicePhase, PrivateBazaarWorkerSupervisor,
};
#[cfg(feature = "private-bazaar-live")]
pub use private_bazaar_targets::{
    PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV, PrivateBazaarCharacterStore,
    PrivateBazaarDurableTargetRegistry, PrivateBazaarFileSigningCustody,
    PrivateBazaarTargetRegistryError,
};
#[cfg(feature = "private-bazaar-live")]
pub use private_bazaar_worker::{
    FinalizedPrivateBazaarReceipt, FinalizedPrivateBazaarReceiptSource, PrivateBazaarFileWorker,
    PrivateBazaarReceiptSpool, PrivateBazaarWorkerError, PrivateBazaarWorkerListener,
    PrivateBazaarWorkerPoll, PrivateBazaarWorkerRun, PrivateBazaarWorkerTargets,
};
#[cfg(feature = "private-fhegg-game-consequence")]
pub use private_fhegg_game_consequence::{
    FaithfulSpendGameAuthorityReceipt, PrivateFheggGameConsequenceError,
    PrivateFheggGameConsequenceGate, PrivateFheggGameConsequenceReceipt, PrivateFheggGameMechanic,
    PrivateFheggWinnerRoute,
};
#[cfg(feature = "private-fhegg-game-consequence")]
pub use shielded_crown_orchestration::{
    ShieldedCrownAction, ShieldedCrownHand, ShieldedCrownOrchestrationError, ShieldedCrownPolicy,
    execute_shielded_crown_action,
};
#[cfg(feature = "private-fhegg-game-consequence")]
pub use shielded_dungeon_publication::{
    ShieldedDungeonPublicCard, ShieldedDungeonPublicationError,
};

/// **The platform-independent inputs a catalog registration needs** — everything a frontend
/// must decide before the shared list can be registered. All plain `Send` data (raw pubkeys,
/// numbers), so it crosses into a `HostThread::spawn` build closure freely.
///
/// The defaults reproduce today's deployed registrations byte-for-byte (quorum 2, the two
/// candidate proposals, grain budget 1000) so a frontend's cutover to [`build_full_catalog`]
/// is behavior-preserving; only the electorate has no honest default (an empty electorate is
/// a council nobody can vote in — deliberate, so a frontend MUST derive and supply one).
#[derive(Debug, Clone)]
pub struct CatalogConfig {
    /// The council electorate: member Ed25519 public keys. A member's on-substrate identity is
    /// `hex(pubkey)`, so a frontend makes user U a voter by deriving U's platform identity to a
    /// pubkey and listing it here — web derives `blake3(username)` (demo-grade), Telegram
    /// `TelegramCipherclerk::derive(bot_secret, uid)`, Discord
    /// `UserCipherclerk::derive(bot_secret, user_id, federation_id)`.
    pub council_members: Vec<[u8; 32]>,
    /// Council quorum M — a proposal enacts once M members approve
    /// (`CouncilOffering::new`'s `quorum_m: u64`). Deployed default: 2.
    pub council_quorum: u64,
    /// The council's candidate proposals. Deployed default: the two every surface registers
    /// today ("Fund the archive" 42 · "Ratify the charter" 7).
    pub council_proposals: Vec<CandidateProposal>,
    /// The grain offering's spend budget (`GrainOffering::new`'s `budget: i64`).
    /// Deployed default: 1000.
    pub grain_budget: i64,
    /// **The day the native Descent (and the campaign over it) mints its banked relics under.**
    /// See [`DescentDayBinding`]; the deployed live answer is [`DescentDayBinding::Live`], which every
    /// frontend gets by building this with [`CatalogConfig::live`].
    pub descent_day: DescentDayBinding,
}

/// **Where a catalog's Descent gets the provenance root its banked relics mint under.**
///
/// A banked relic's note is content-addressed to `(run day-seed, custody slot, player key)`, so
/// this is exactly the difference between a relic id anyone can compute in advance and one that
/// could not exist before a drand round was revealed.
#[derive(Debug, Clone, Copy, Default)]
pub enum DescentDayBinding {
    /// The reproducible root derived from the deploy seed — pre-computable. Right for a
    /// fixture or an offline replay, WRONG for a surface serving players. The [`Default`],
    /// because a config that has not been told about a beacon must not pretend it has one.
    #[default]
    SeedDerived,
    /// One verified beacon day, frozen for this host's lifetime. Honest for a single-day
    /// fixture or a replay of a known day; a long-lived host wants [`Live`](Self::Live),
    /// since this one keeps minting the day it was registered on.
    Fixed(CommittedSeed),
    /// **The deployed posture: resolved at EVERY open** from a source the frontend refreshes
    /// (see [`todays_descent_day`] / [`publish_todays_descent_day`]). No verified day right
    /// now ⇒ the open is REFUSED, never silently served on the pre-computable root.
    Live(fn() -> Option<CommittedSeed>),
}

impl Default for CatalogConfig {
    fn default() -> Self {
        CatalogConfig {
            council_members: Vec::new(),
            council_quorum: 2,
            council_proposals: vec![
                CandidateProposal::new("Fund the archive", 42),
                CandidateProposal::new("Ratify the charter", 7),
            ],
            grain_budget: 1000,
            descent_day: DescentDayBinding::default(),
        }
    }
}

impl CatalogConfig {
    /// A config with the given electorate and every other knob at its deployed default —
    /// the constructor the three chat frontends' `*_default_host(members)` bodies become.
    pub fn with_council_members(council_members: Vec<[u8; 32]>) -> Self {
        CatalogConfig {
            council_members,
            ..CatalogConfig::default()
        }
    }

    /// **THE LIVE-SURFACE CONFIG.** Identical to
    /// [`with_council_members`](Self::with_council_members) except that the Descent (and the
    /// campaign over it) mints its banked relics under the CURRENT verified beacon day,
    /// re-resolved at every open through [`todays_descent_day`].
    ///
    /// Every frontend that serves players builds its host through this, and keeps the day fresh
    /// by calling [`publish_todays_descent_day`] at startup and on each roll. Until a day is
    /// published, opening the Descent REFUSES — deliberately: a live surface must not serve a
    /// pre-computable provenance root just because the beacon fetch has not landed yet.
    pub fn live(council_members: Vec<[u8; 32]>) -> Self {
        CatalogConfig {
            descent_day: DescentDayBinding::Live(todays_descent_day),
            ..CatalogConfig::with_council_members(council_members)
        }
    }

    /// A config pinned to ONE verified beacon day — the reveal is BLS-verified here
    /// (`DailyBeacon::seed` pairs against the pinned quicknet group key before it derives
    /// anything), so a forged or mutated reveal yields no config and no day at all. For a
    /// single-day fixture or the replay of a known day; a serving host wants
    /// [`live`](Self::live).
    pub fn on_beacon(
        council_members: Vec<[u8; 32]>,
        beacon: &DailyBeacon,
    ) -> Result<Self, VerifyError> {
        Ok(CatalogConfig {
            descent_day: DescentDayBinding::Fixed(beacon.seed()?),
            ..CatalogConfig::with_council_members(council_members)
        })
    }

    /// The native Descent offering this config's day binding calls for — the ONE place the
    /// catalog decides whether a live run's relic provenance is beacon-bound. Public so a
    /// canary can drive the EXACT offering `register_games` mounts, rather than a re-authored
    /// peer of it.
    pub fn native_descent(&self) -> NativeDescentOffering {
        match self.descent_day {
            DescentDayBinding::SeedDerived => NativeDescentOffering::new(),
            DescentDayBinding::Fixed(day) => NativeDescentOffering::on_day(day),
            DescentDayBinding::Live(source) => NativeDescentOffering::on_day_source(source),
        }
    }
}

/// The process-wide published day: `(UTC day number, that day's verified committed seed)`.
static TODAYS_DESCENT_DAY: OnceLock<Mutex<Option<(u64, CommittedSeed)>>> = OnceLock::new();

fn todays_descent_day_cell() -> &'static Mutex<Option<(u64, CommittedSeed)>> {
    TODAYS_DESCENT_DAY.get_or_init(|| Mutex::new(None))
}

/// **Publish the verified beacon for `utc_day`** as the day every catalog-registered Descent
/// mints its banked relics under. The reveal is BLS-verified HERE (`DailyBeacon::seed` runs the
/// pairing check against the pinned quicknet group key before it derives anything), so a forged
/// or mutated round publishes NOTHING and returns the verify error — you cannot install a
/// forged day, and you cannot grind a favourable one.
///
/// A frontend calls this once at startup with the beacon it resolved
/// (`procgen_dregg::beacon::todays_beacon`, whose result also says whether the round is live or
/// the labeled pinned fallback) and again whenever the UTC day rolls.
pub fn publish_todays_descent_day(utc_day: u64, beacon: &DailyBeacon) -> Result<(), VerifyError> {
    let seed = beacon.seed()?;
    *todays_descent_day_cell()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some((utc_day, seed));
    Ok(())
}

/// **Today's published day, or `None`** — the [`DescentDayBinding::Live`] source. `None` (⇒ the open
/// is refused) whenever no day has been published, or the published one is not today's: a day
/// that has rolled is stale, and serving yesterday's provenance root under today's play would
/// make the day's relic ids computable by anyone who played yesterday.
pub fn todays_descent_day() -> Option<CommittedSeed> {
    let today = procgen_dregg::beacon::current_utc_day();
    todays_descent_day_cell()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .and_then(|(day, seed)| (day == today).then_some(seed))
}

/// **The offline day: publish the PINNED published round for today.** For drives with no egress
/// — an integration test, a boxed demo — where the live binding must still be exercised rather
/// than swapped for the seed-derived one.
///
/// It is a REAL, BLS-verifiable drand reveal (it is what [`refresh_todays_descent_day`] serves,
/// clearly labeled, when the transport is down), so the whole verify path runs for real. ⚠ It is
/// NOT today's round: a fixed published round is as pre-computable as any constant, so this
/// establishes the WIRING is beacon-bound and establishes nothing about unpredictability. A
/// serving process calls [`refresh_todays_descent_day`], never this.
pub fn publish_pinned_descent_day() -> Result<(), VerifyError> {
    publish_todays_descent_day(
        procgen_dregg::beacon::current_utc_day(),
        &procgen_dregg::beacon::pinned_fallback_beacon(),
    )
}

/// **Fetch today's drand round and publish it as the Descent's day** — the one beacon-source
/// wiring every live frontend runs: once at boot, and again on a timer so the binding does not
/// go stale when the UTC day rolls (a rolled day resolves to `None` and REFUSES opens, which is
/// the fail-closed behaviour, not a working one).
///
/// Blocking (it makes an HTTP request): drive it off a `spawn_blocking`. It rides
/// [`procgen_dregg::beacon::todays_beacon`], so a fetched round that does not parse or does not
/// pass the BLS pairing check is a HARD error that publishes nothing, and only a *transport*
/// failure falls back — to the pinned published round, itself re-verified, returned LABELED as
/// [`BeaconSource::PinnedFallback`] with its staleness. Callers must log that label: the pinned
/// round is a real reveal but not today's, so during a fallback window the day's relic
/// provenance is predictable to anyone who knows the pinned round.
pub fn refresh_todays_descent_day(api_base: &str) -> Result<BeaconSource, FetchError> {
    let resolved = procgen_dregg::beacon::todays_beacon(&HttpRoundFetch, api_base)?;
    publish_todays_descent_day(procgen_dregg::beacon::current_utc_day(), &resolved.beacon)
        .map_err(FetchError::Verify)?;
    Ok(resolved.source)
}

/// **THE seam: register the full DreggNet portfolio into `host`.** Nine games + nine RPG
/// feature surfaces + five service offerings = the 23 every frontend exposes. Call it inside
/// the frontend's host-build closure (on the host's owning thread) so `!Send` offering
/// internals are born confined, exactly as the four per-frontend registrars do today.
pub fn build_full_catalog(host: &mut OfferingHost, cfg: &CatalogConfig) {
    register_games(host, cfg);
    register_feature_surfaces(host);
    register_services(host, cfg);
    // ⚑ All 23 stay MOUNTED and openable; [`apply_ship_list`] only decides which of them a
    // browse list paints. The list itself is [`SHIPPED_KEYS`] — one array, one edit.
    apply_ship_list(host);
}

/// Build a fresh [`OfferingHost`] carrying the full catalog — the convenience every
/// `*_default_host` collapses into (`HostThread::spawn(move || full_catalog_host(&cfg))`).
pub fn full_catalog_host(cfg: &CatalogConfig) -> OfferingHost {
    let mut host = OfferingHost::new();
    build_full_catalog(&mut host, cfg);
    host
}

/// **The nine portfolio games** — native Descent · Descent campaign · dungeon · council ·
/// market · Dark Bazaar · tug · automatafl · proof-assigned tactical raid.
/// Port source (titles + shapes, byte-identical across the three existing copies):
/// `dreggnet-web/src/lib.rs:1232-1282` / `dreggnet-telegram/src/host.rs:419-451`.
pub fn register_games(host: &mut OfferingHost, cfg: &CatalogConfig) {
    // ⚑ The Descent and the campaign over it both deploy on `cfg`'s day binding: with
    // `descent_day` set (the live `CatalogConfig::on_beacon` path) every run this host opens
    // mints its banked relics under a provenance root derived from that day's verified drand
    // reveal, so no relic id exists — to anyone — before the round matures.
    host.register(
        "descent",
        // ⚑ A SHIPPED TITLE, so it is read by a stranger before anything else on the shelf. It used
        // to say "the Lean-authored custody dungeon (delve · unlock · smite · loot · bank)" — four
        // private terms and the engine's own verb list. Every clause below is the game's, read out
        // of `dungeon_on_dregg::descent`: BREATH is spent by every verb and never refills, the day
        // picks one of DAYS maps, and `flee` banks only what is CARRIED (floor relics stay).
        "The Descent — a solo dungeon crawl on one torch of light. Everyone gets the same dungeon today, and you keep only what you carry back out.",
        cfg.native_descent(),
    );
    host.register(
        DescentCampaignOffering::KEY,
        "The Deepening Ways — player-driven native Descent expeditions; only a replay-verified Crown opens each real region road",
        DescentCampaignOffering::with_native(cfg.native_descent()),
    );
    host.register(
        "dungeon",
        "The Warden's Keep — a verifiable dungeon (offering #0)",
        DungeonOffering::new(),
    );
    host.register(
        "council",
        // ⚑ `vote` IS NOT A VERB HERE — the ballot is two, `TURN_APPROVE` and `TURN_REJECT`, and a
        // member casts exactly one of them per proposal (write-once). Found by the same sweep that
        // caught `grain` and `hermes`; two of the three named verbs were right, which is why it
        // had never been noticed.
        "DreggNet Council — propose something, and every member approves or rejects it once. Once enough have approved, anyone can enact it; until then enacting is refused. Only members can act at all.",
        CouncilOffering::new(
            cfg.council_members.clone(),
            cfg.council_proposals.clone(),
            cfg.council_quorum,
        ),
    );
    host.register(
        "market",
        "DreggNet Market — a sealed-bid auction (list · bid · settle)",
        MarketOffering::new(),
    );
    host.register(
        DarkBazaarOffering::KEY,
        // ⚑ "CRAWL" IS A GRADE, NOT A GENRE, and a stranger reads it as the latter. In this
        // workspace the word is a rung on a privacy ladder
        // (`DARK_BAZAAR_CRAWL_DISCLOSURE`: "CRAWL grade: operator-visible-at-settle /
        // check-level. NOT Tier0 house-blind…", `docs/deos/THE-DARK-BAZAAR.md`) — it means the
        // FIRST, weakest tier. On a shelf beside a dungeon called The Descent it reads as
        // "playable dungeon crawl", and `DarkBazaarOffering` has no movement, no map and no
        // encounter state: it wraps `MarketOffering` whole and renames three buttons. What it
        // genuinely adds over `market` is the disclosure, so the disclosure is what the line says.
        "The Dark Bazaar — the sealed-bid auction, with the privacy spelled out. Your number is hidden from the other bidders until the auction clears; it is not hidden from whoever runs the server, and it never was.",
        DarkBazaarOffering::new(),
    );
    // `tug` needs the seat-claiming adapter: `TugOffering` names its two seats by fixed
    // canonical strings while every frontend's user identity is a derived key, so the ONE
    // shared `seated::SeatedTug` (port of `dreggnet-web/src/seated.rs`, collapsing the
    // telegram/wechat/discord byte-peers) claims seats for the first two identities that act.
    host.register(
        "tug",
        // ⚑ "seven guilds" read as seven PLAYERS to a stranger; it is seven scoring lanes in a
        // TWO-seat game (`N_GUILDS = 7`, `Player` has two variants). "You cut, they choose" is
        // exact — a Gift or Competition only presents cards, and the responder takes one share
        // while the proposer keeps the other — but it needed a subject.
        "Multiway-Tug — two hidden hands of cards pulling at seven contested lanes. You cut the offer; your opponent chooses which side they take.",
        seated::SeatedTug::new(),
    );
    host.register(
        "automatafl",
        // ⚑ The old tagline named the three phases of the round rather than the game. Both clauses
        // are the ruleset's: no move executes until both seats have sealed and opened, and the
        // automaton is the one piece neither seat may move (`moveLegalB` bans it as a source) and
        // the only one that wins the game.
        "Automatafl — two players move at the same time, in secret, and the piece that decides it is the one neither of you controls.",
        AutomataflOffering,
    );
    host.register(
        dreggnet_surfaces::private_raid::KEY,
        "The Ash Gate Raid — muster four identities · verify a shielded optimal role assignment · fight through real party capabilities",
        HostedProofAssignedRaidOffering::new(),
    );
}

/// **The nine do-once RPG feature surfaces** — trade · inventory · cheevos · guild · craft ·
/// companion · quest · tavern · party. The asset-bearing surfaces share one `SharedWorld` (so
/// craft → inventory → trade compose over one ledger).
///
/// ⚠ **ANONYMOUS / SINGLE-PLAYER ONLY.** The world this mounts belongs to
/// [`dreggnet_surfaces::DEMO_PLAYER`] and is shared by every session on the host, so on a host
/// serving more than one viewer *every player shares one inventory*. A frontend with identified
/// viewers routes the eight [`is_rpg_key`] keys to a per-identity host from [`PlayerWorlds`]
/// instead, and keeps `party` plus the other shared tables on this global host.
pub fn register_feature_surfaces(host: &mut OfferingHost) {
    dreggnet_surfaces::register_surfaces(host);
}

/// **The five non-game service offerings** — doc · names · compute · grain · hermes.
/// Complete port of the byte-identical `dreggnet-web/src/lib.rs:1296-1322`
/// (`register_non_game_offerings`) / `dreggnet-telegram/src/host.rs:457-482`, with the grain
/// budget lifted from a duplicated magic `1000` into [`CatalogConfig::grain_budget`].
pub fn register_services(host: &mut OfferingHost, cfg: &CatalogConfig) {
    host.register(
        "doc",
        // ⚑ NONE OF THE THREE VERBS EXISTED. `DocOffering`'s vocabulary is `insert` · `delete` ·
        // `set_title` · `resolve_title` · `order_conflict`; there is no `author`, no `amend` and no
        // `verify` affordance. "Store" was wrong too — it is a live multi-editor document whose
        // whole point is what happens when two people edit at once.
        //
        // ⚠ And the last clause is not padding: `actions_for` enables an edit only for an identity
        // holding the region's edit cap, a freshly-opened document has an empty roster, and there
        // is no join seam — so a first visitor really is served three dimmed controls and no way
        // in. That is a NAMED open gap (`dreggnet-web/tests/catalog_flow_harness.rs`'s `doc`
        // allowance, a cap-model decision, not a patch). A line that omitted it would be selling a
        // document nobody can write in.
        "DreggNet Doc — a document several people write at once. Two edits made at the same moment are held side by side until somebody picks the order, instead of one of them quietly winning. ⚠ You cannot type in it yet: only an invited editor may edit, and a freshly opened document has no editors and no way to become one, so every control starts greyed out.",
        dreggnet_doc::DocOffering::new(),
    );
    host.register(
        "names",
        // The three verbs are REAL (`TURN_REGISTER`/`TURN_TRANSFER`/`TURN_RESOLVE`). The warning
        // is: `NamesSession::enroll` — which mints the actor's signer and stands up its executor —
        // is reachable only from this crate's own tests and from `replay`, so `open` starts with an
        // EMPTY actor map and every verb refuses at `do_register`'s first line. A NAMED open gap
        // (`dreggnet-web/tests/catalog_flow_harness.rs`'s `names` allowance). Leaving it unsaid
        // while the sibling lines got honest is the exact laundering this pass exists to undo.
        // The verbs are listed as PROSE, not in the `(a · b · c)` slot, and that is deliberate: at
        // genesis the surface presents only `register`, so `transfer` and `resolve` — which do
        // exist — are unreachable until a name lands, and no name can land. Advertising three
        // verbs a player can reach none of is the same shape as advertising three that do not
        // exist.
        "DreggNet Names — claim a short name, look one up, or hand one to someone else. ⚠ Nothing lands from here yet: each of those refuses because you are not enrolled, and this surface has no way to enrol you.",
        dreggnet_names::NamesOffering::new(),
    );
    host.register(
        "compute",
        // ⚑ The three verbs were RIGHT (`TURN_POST`/`TURN_CLAIM`/`TURN_SETTLE` all exist and all
        // land); "confined compute-job" was the lie. `dreggnet_compute`'s own `[HONEST SCOPE]`
        // note says the confined EXECUTION is stubbed: `do_settle` accepts any non-empty string as
        // "the result" and nothing binds it to the sealed job spec. So the line names the two
        // things that ARE real and enforced (one claimant; a settlement the executor checks adds
        // up) and states the two absences instead of implying them away.
        "DreggNet Compute — put a budget on a job, let one worker claim it at their price, then release it when they hand back a result. The release always adds up exactly: the worker's price plus the refund equals the budget. It never runs the job and never checks the result, and the budget is bookkeeping on the job rather than money leaving anyone's pocket.",
        dreggnet_compute::ComputeOffering::new(),
    );
    host.register(
        "grain",
        // ⚑ NEITHER VERB EXISTED. `GrainOffering` has exactly one, `TURN_ACT` ("act"); there is no
        // `request` and no `grant`. And "spend budget" named the wrong meter: the cap the executor
        // enforces is `calls_made ≤ rate_limit` — a COUNT OF TURNS — while the action's `cost`
        // accumulates into `consumed` purely as witness state and binds nothing (`grain-turn`:
        // "there is no per-call charge on the grain grant, so no charge `Transfer` rides").
        "DreggNet Grain — a hard allowance you can spend down and cannot talk your way past. Every press uses one of this grain's turns; when they run out, the next press is refused underneath rather than greyed out here. The allowance counts turns, not money, and a turn does no work of its own yet — the limit is the thing on show.",
        dreggnet_grain::GrainOffering::new(cfg.grain_budget),
    );
    host.register(
        "hermes",
        // ⚑ THERE IS NO RELAY. No recipient, no mailbox, no delivery and no ack exist anywhere in
        // `dreggnet-hermes`: a `HermesSession` is ONE agent runtime for ONE party in ONE process,
        // and its only verb is `TURN_PROMPT`. What it really is: you type a message, an on-box
        // keyless brain (or a BYO-key provider) sorts it into a class of tool, and the executor
        // admits or refuses that class against its own rate + value allowance. The tool itself is
        // never run — `drive` invokes with an EMPTY work witness, which the crate calls the named
        // seam — so the line says that rather than letting "relay" imply a message arrived.
        "DreggNet Hermes — an AI agent kept on a short leash. Type it a message and it picks what kind of work it wants — read, search, fetch, run, edit or just talk — and each kind has its own allowance. Ask past one and the request is turned down, naming the limit that stopped it. The work is never actually carried out: what you are watching is the permission, granted or refused.",
        dreggnet_hermes::HermesOffering::new(),
    );
}

/// The 23 catalog keys, in registration order — the parity contract. Every frontend's
/// "which offerings exist" question resolves to this ONE list; the test below pins
/// `full_catalog_host` to it, and a frontend cutover test can pin its old registrar against
/// the same constant before deleting it.
pub const CATALOG_KEYS: [&str; 23] = [
    // games
    "descent",
    DescentCampaignOffering::KEY,
    "dungeon",
    "council",
    "market",
    "bazaar",
    "tug",
    "automatafl",
    dreggnet_surfaces::private_raid::KEY,
    // feature surfaces (dreggnet_surfaces::register_surfaces order)
    "trade",
    "inventory",
    "cheevos",
    "guild",
    "craft",
    "companion",
    "quest",
    "tavern",
    "party",
    // services
    "doc",
    "names",
    "compute",
    "grain",
    "hermes",
];

// ═════════════════════════════════════════════════════════════════════════════
// ⚑ THE SHIP LIST — the ONE place that decides what we ADVERTISE
// ═════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE SHIP LIST. Edit THIS ARRAY to change what the public shelves show.**
///
/// [`CATALOG_KEYS`] is what EXISTS (23 offerings, all mounted, all openable). This is what we
/// **advertise**: the small set we are actually ready to put in front of a stranger. Everything
/// registered and not named here stays mounted, openable by key or URL, and fully playable — it
/// simply is not on any shelf, in any menu, or in any bot's picker.
///
/// **To re-list an offering: add its key to this array. That is the whole change.** To take one
/// off the shelf: delete its key. Nothing else moves — no route, no crate, no registration.
///
/// Where it takes effect (all downstream of this one array):
/// - [`apply_ship_list`] marks every other registered key unadvertised on the host, so
///   `OfferingHost::list_advertised_offerings` — which the web catalog page, the Telegram
///   `/offerings` + `/play` menus, the WeChat menu, the Telegram Mini App and the Discord
///   Activity all paint — carries only these.
/// - the discord-bot builds no `OfferingHost`, so it reads [`is_shipped`] directly in its
///   `/play` choice list.
///
/// **Why these three** (measured 2026-07-26 over `git log`, per-crate test counts, and the
/// Lean sources each rides):
/// - `descent` — the flagship. Its own code has the deepest recent history, it is the only
///   offering with a bespoke served play surface *and* a durable leaderboard that re-verifies
///   every stored run by replay on boot, and the landing already funnels to it.
/// - `automatafl` — the most-worked game by every measure: its own crate, a Lean-authored
///   rule set and AIR with a differential oracle test, a dedicated board front door, and a
///   seat-locked table door. The one surface a first-time reader could actually act on.
/// - `tug` — a Lean spec (`Dregg2/Games/MultiwayTug*.lean`) with an FFI oracle probe pinning
///   the Rust engine to it, its own front door and table door.
///
/// Everything else is real work in progress, not a thing to hand a stranger: the nine RPG
/// feature surfaces are demo mounts (four are literally registered from `::demo(…)`
/// constructors, and trade/inventory/craft share ONE world named `"Adventurer"` across every
/// viewer of a host), and no service crate carries a fraction of the effort the three games do.
pub const SHIPPED_KEYS: [&str; 3] = ["descent", "automatafl", "tug"];

/// Whether `key` is on the [ship list](SHIPPED_KEYS) — i.e. whether we advertise it.
///
/// ⚠ NOT an access check. An unshipped offering is still registered, still openable, and still
/// verifiable; this only answers "does it go on a shelf".
pub fn is_shipped(key: &str) -> bool {
    SHIPPED_KEYS.contains(&key)
}

/// **Stamp the [ship list](SHIPPED_KEYS) onto `host`** — every registered key not in
/// [`SHIPPED_KEYS`] is marked unadvertised, every key in it is marked advertised.
///
/// [`build_full_catalog`] calls this last, so EVERY frontend that builds its host through the
/// shared registrar inherits the same shelf without doing anything. A frontend that registers
/// extra offerings of its own after `build_full_catalog` should call this again (or
/// `set_advertised` for its own key) — a later `register` does not re-apply it.
pub fn apply_ship_list(host: &mut OfferingHost) {
    for key in host.keys() {
        let shipped = is_shipped(&key);
        host.set_advertised(&key, shipped);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE FRONT-DOOR COPY — the one place the shelf's product words live
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE NAME OF THE PLAY SURFACE, in ONE place.** `Dragon's Arcade` — the shelf a stranger
/// arrives at, deployed at `arcade.dregg.net`, painted by every host that builds its catalog
/// through this crate (the web top bar and every `<title>`, the Telegram Mini App entry, the
/// WeChat menu card, the discord-bot's admin portal).
///
/// **It does NOT rename the project.** `dregg` is the project, the workspace, the token and the
/// `www.dregg.net` domain, and none of that moves; this names the ARCADE — the one surface people
/// play on. The two are related the way a storefront is related to the company: exactly one place
/// says both, [`arcade_lineage`], which every page footer carries.
///
/// It is also NOT `DreggNet Cloud`. That phrase names the frontend-agnostic Offering/Session
/// *library layer*, and `docs/DREGGNET-CLOUD-OFFERINGS.md` says outright that it "names the shape,
/// not a live service" — correct in the library docs, wrong in a browser tab.
///
/// The apostrophe is the ASCII `'`, deliberately: it survives a `<title>`, a Telegram plain-text
/// message, a grep and a terminal identically, and no HTML escaper in this workspace touches it
/// (`dreggnet_web::esc` escapes `& < > "` only).
pub const SURFACE_NAME: &str = "Dragon's Arcade";

/// **The one line that says both names** — where the arcade sits inside the project. Every host's
/// footer/about carries this and nothing else does, so "Dragon's Arcade" reads as a product and
/// `dregg` stays the project without either name being repeated into noise.
pub fn arcade_lineage() -> &'static str {
    "Dragon's Arcade is the play surface of the dregg project."
}

/// **The shelf intro** — the sentence every catalog LISTING leads with, on every front door (web
/// `GET /offerings`, the Mini App `/tg` fragment, Telegram `/offerings`, Discord `/play`). ONE
/// string, so the front doors cannot drift into different stories about what this is.
///
/// ⚑ Written for someone who has never heard of this project: it names what you get (games, in a
/// browser) BEFORE it makes any claim, and it makes the honest claim in words a newcomer owns —
/// no `executor`, no `substrate`, no `receipt`, no `turn`. It used to open "🧪 The Lab —
/// experimental engine surfaces… on the shelf for the curious", which was accurate about 23
/// experiments and is the wrong thing to say about a curated shelf ([`SHIPPED_KEYS`]).
pub fn shelf_intro() -> &'static str {
    "🎲 Games you can play right now, in a browser tab — no install, no wallet, no sign-up. \
     Every move you make is re-run against the rules before it is recorded, so an illegal move \
     is refused rather than accepted, and a finished game can be replayed by anyone who wants \
     to check it really went that way."
}

/// **The flagship pointer** — where the game begins. The Descent is registered in the common
/// catalog so web, Telegram, and Discord all drive the same rules; dedicated `/descent` routes
/// provide richer presentation over that same core.
///
/// Same rule as [`shelf_intro`]: a stranger has to be able to picture the game. It used to read
/// "the Lean-authored custody dungeon… exercise attenuating keys… bank only on a proved exit",
/// four private terms in one sentence.
pub fn flagship_pointer() -> &'static str {
    "⚔️ The Descent — a dungeon crawl. Everyone gets the same dungeon each day, built from a \
     public random number nobody can pick in advance. One life, no retries: go deeper for better \
     loot, and you only keep what you carry back out."
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The parity contract: the full catalog registers exactly [`CATALOG_KEYS`] — the same 23
    /// `dreggnet_web::demo_host()` serves today. (Once the frontends delegate here, this is the
    /// single test that "add an offering" must update, and drift is a compile-time/test failure
    /// instead of a fourfold folklore.)
    #[test]
    fn the_full_catalog_registers_exactly_the_contract_keys() {
        let cfg = CatalogConfig::default();
        let host = full_catalog_host(&cfg);
        let mut keys: Vec<String> = host.list_offerings().into_iter().map(|o| o.key).collect();
        keys.sort();
        let mut want: Vec<&str> = CATALOG_KEYS.to_vec();
        want.sort();
        assert_eq!(keys, want);
    }

    /// **The ship list names only real offerings, and it is what a shelf paints.** Both
    /// directions, so a typo in [`SHIPPED_KEYS`] (a key nothing registers) fails here rather than
    /// silently shrinking every shelf on the platform.
    #[test]
    fn the_shelf_is_exactly_the_ship_list() {
        let host = full_catalog_host(&CatalogConfig::default());
        for key in SHIPPED_KEYS {
            assert!(
                host.has(key),
                "SHIPPED_KEYS names `{key}`, which nothing registers"
            );
        }
        let mut shelf: Vec<String> = host
            .list_advertised_offerings()
            .into_iter()
            .map(|o| o.key)
            .collect();
        shelf.sort();
        let mut want: Vec<String> = SHIPPED_KEYS.iter().map(|k| k.to_string()).collect();
        want.sort();
        assert_eq!(shelf, want, "the advertised shelf IS `SHIPPED_KEYS`");
        assert!(
            host.list_offerings().len() > shelf.len(),
            "and the FULL registry is still bigger — unlisted is not deleted"
        );
    }

    /// ⚑ **UNLISTED IS NOT DELETED.** Every offering we took off the shelf still deploys, still
    /// takes a turn, and still verifies for anyone holding its key — the ship list is an
    /// advertising decision, and this is the test that keeps it one.
    #[test]
    fn every_unshipped_offering_still_opens_and_verifies_by_key() {
        use dreggnet_offerings::{SessionConfig, SessionId};

        let mut host = full_catalog_host(&CatalogConfig::default());
        for key in CATALOG_KEYS {
            if is_shipped(key) {
                continue;
            }
            assert!(!host.is_advertised(key), "{key} is off the shelf");
            assert!(host.has(key), "…but `{key}` is still MOUNTED");
            let id = SessionId::new(format!("unlisted-{key}"));
            // The routing property is the one that matters: the key must never become
            // `UnknownOffering`. An offering may still refuse its own deploy for its own reasons
            // (that is its business, and identical to before the ship list existed).
            match host.open_session(key, id.clone(), SessionConfig::with_seed(11)) {
                Ok(()) => {
                    assert!(
                        host.render(key, &id).is_some(),
                        "unlisted `{key}` opened, so it must still render"
                    );
                    // The VERIFIER must still be reachable. Its verdict on a genesis-only
                    // session is the offering's own business (`market`, for one, does not
                    // report `verified` on an empty book) and has nothing to do with the shelf.
                    assert!(
                        host.verify(key, &id).is_some(),
                        "unlisted `{key}` opened, so its verifier must still be mounted"
                    );
                }
                Err(dreggnet_offerings::HostError::UnknownOffering(k)) => {
                    panic!("taking `{k}` off the shelf must NOT unroute it")
                }
                Err(_) => {}
            }
        }
    }

    /// ⚑ **A TITLE MAY NOT NAME A VERB THE OFFERING DOES NOT HAVE.**
    ///
    /// The wound this closes, measured 2026-07-26 over the registrations above: `grain` advertised
    /// "(request · grant)" and `GrainOffering` has exactly one verb, `act`; `hermes` advertised
    /// "the message relay (send · deliver · ack)" and there is no recipient, mailbox, delivery or
    /// ack anywhere in the crate; `doc` advertised "(author · amend · verify)" against a vocabulary
    /// of `insert`/`delete`/`set_title`/`resolve_title`/`order_conflict`; `council` advertised
    /// "vote" where the ballot is `approve` and `reject`. Four of the five verb lists on this shelf
    /// named a program that did not exist, and every one of them compiled, rendered and shipped —
    /// because a title is a string and nothing had ever compared it to an affordance.
    ///
    /// The check: any `(a · b · c)` list in a registered title must consist of verbs the offering
    /// really presents. The vocabulary is collected from the offering ITSELF — its genesis
    /// affordances, plus the affordances it presents after each genesis move is driven once, which
    /// is what reaches a lifecycle verb like the market's `bid`/`settle` that genesis cannot offer.
    ///
    /// It is deliberately a check on the WORDS THAT LOOK LIKE VERBS, not on prose: a title with no
    /// parenthesised `·` list (every one this pass rewrote) is simply not constrained here, because
    /// prose is a claim about behaviour and no test can hold that. This holds the one part that is
    /// mechanically checkable, and holds it completely.
    #[test]
    fn no_registered_title_names_a_verb_the_offering_does_not_have() {
        use dreggnet_offerings::{SessionConfig, SessionId};

        /// Every verb a title ADVERTISES: scan each parenthesised group, and for any group
        /// carrying a `·` take the FIRST WORD of each element.
        ///
        /// First-word, not whole-element, because the house shape is a verb with its object
        /// attached — `(list · settle an atomic asset swap)`, `(consume materials · mint a bound
        /// output)`. Reading only the single-word elements would have let exactly those two
        /// through, and both were wrong: `trade`'s verbs are `list`/`buy`/`cancel` (no `settle`
        /// anywhere) and `craft`'s single verb is `craft` (no `consume`, no `mint`).
        ///
        /// The corollary is that a parenthesised `·` list is RESERVED for verbs. A NOUN list in
        /// that shape (`inventory` shipped "(gear · cards · trophies)") reads to a player as
        /// "these are the things you can do" and to this gate as three missing verbs — so the
        /// convention is enforced rather than special-cased.
        fn advertised_verbs(title: &str) -> Vec<String> {
            let mut out = Vec::new();
            let mut rest = title;
            while let Some(open) = rest.find('(') {
                let after = &rest[open + 1..];
                let Some(close) = after.find(')') else { break };
                let inner = &after[..close];
                let single_verb = !inner.trim().contains(char::is_whitespace)
                    && inner
                        .trim()
                        .chars()
                        .all(|c| c.is_ascii_lowercase() || c == '_' || c == '-')
                    && !inner.trim().is_empty();
                if inner.contains('·') || single_verb {
                    out.extend(
                        inner
                            .split('·')
                            .filter_map(|element| element.split_whitespace().next())
                            .map(str::to_string),
                    );
                }
                rest = &after[close + 1..];
            }
            out
        }

        /// The advertised verbs NOTHING in the offering's vocabulary backs — the whole verdict, as
        /// a function, so the same comparison the shelf is judged by can itself be shown to bite.
        fn unbacked<'a>(
            advertised: &'a [String],
            vocabulary: &std::collections::BTreeSet<String>,
        ) -> Vec<&'a String> {
            advertised
                .iter()
                .filter(|verb| !vocabulary.contains(*verb))
                .collect()
        }

        let cfg = CatalogConfig::default();
        let mut host = full_catalog_host(&cfg);
        let actor = dreggnet_offerings::DreggIdentity("verb-census".to_string());

        let mut checked = 0usize;
        for key in CATALOG_KEYS {
            let title = host.title(key).unwrap_or_default().to_string();
            let advertised = advertised_verbs(&title);
            if advertised.is_empty() {
                continue;
            }
            let id = SessionId::new(format!("verbs-{key}"));
            if host
                .open_session(key, id.clone(), SessionConfig::with_seed(5))
                .is_err()
            {
                // An offering may refuse its own deploy for its own reasons (the live Descent day
                // binding, for one). It then advertises nothing to check against, and saying so is
                // better than passing quietly.
                panic!(
                    "`{key}` advertises the verbs {advertised:?} in its title but will not open, \
                     so the claim cannot be checked at all"
                );
            }

            let genesis = host.actions_for(key, &id, &actor).unwrap_or_default();
            let mut vocabulary: std::collections::BTreeSet<String> =
                genesis.iter().map(|a| a.turn.clone()).collect();
            // …plus one step past genesis, which is where a lifecycle verb lives (`market` cannot
            // offer `bid` or `settle` until something is listed, and `trade` cannot offer `buy` or
            // `cancel` until something is). Each probe is its own host so one drive cannot poison
            // the next, and the walk stops the moment the claim is covered — a fresh catalog host
            // is not cheap and there is nothing left to learn once every advertised verb is real.
            for step in genesis {
                if advertised.iter().all(|v| vocabulary.contains(v)) {
                    break;
                }
                let mut probe = full_catalog_host(&cfg);
                let pid = SessionId::new(format!("verbs-{key}-probe"));
                if probe
                    .open_session(key, pid.clone(), SessionConfig::with_seed(5))
                    .is_err()
                {
                    continue;
                }
                if probe.advance(key, &pid, step, actor.clone()).is_none() {
                    continue;
                }
                for action in probe.actions_for(key, &pid, &actor).unwrap_or_default() {
                    vocabulary.insert(action.turn);
                }
            }

            let missing = unbacked(&advertised, &vocabulary);
            assert!(
                missing.is_empty(),
                "`{key}`'s title advertises {missing:?}, which the offering never presents. Its \
                 real vocabulary is {vocabulary:?}.\n  title: {title}"
            );
            checked += 1;
        }

        // ⚑ A GATE THAT CANNOT GO RED IS NOT A GATE. The parser must find lists to check (a
        // regression that broke it would otherwise pass this whole test vacuously), and it must
        // reject a list naming a verb nothing has.
        assert!(
            checked >= 2,
            "the verb-list parser found only {checked} title(s) to check — it has gone blind, and \
             every assertion above passed for free"
        );
        assert_eq!(
            advertised_verbs("X — a thing (list · bid · settle)"),
            vec!["list", "bid", "settle"],
            "the parser reads a verb list"
        );
        assert_eq!(
            advertised_verbs("X (list · settle an atomic asset swap)"),
            vec!["list", "settle"],
            "a verb with its object attached is still an advertised VERB — this exact shape is \
             what hid `trade`'s non-existent `settle`"
        );
        assert_eq!(
            advertised_verbs("Inventory — your gear (gift)"),
            vec!["gift"],
            "a lone lowercase word in the verb slot is a verb list of one"
        );
        assert!(
            advertised_verbs("The Descent — a solo dungeon crawl (one torch of light)").is_empty(),
            "a parenthesised PHRASE with no `·` is not a verb list and must not be checked as one"
        );
        assert!(
            advertised_verbs("The Warden's Keep — a verifiable dungeon (offering #0)").is_empty(),
            "and neither is a parenthesised aside"
        );

        // …and the VERDICT bites, replayed on the exact history this gate was built for: `grain`'s
        // shipped title against `GrainOffering`'s real one-verb vocabulary. Without this the whole
        // test could pass on a `unbacked` that had quietly started returning nothing.
        let grain_as_shipped = advertised_verbs(
            "DreggNet Grain — metered work under a spend budget (request · grant)",
        );
        assert_eq!(grain_as_shipped, vec!["request", "grant"]);
        let grain_reality: std::collections::BTreeSet<String> =
            ["act".to_string()].into_iter().collect();
        assert_eq!(
            unbacked(&grain_as_shipped, &grain_reality).len(),
            2,
            "the verdict must flag BOTH verbs `grain` advertised and never had"
        );
        assert!(
            unbacked(
                &["act".to_string()],
                &["act".to_string()].into_iter().collect()
            )
            .is_empty(),
            "…and must not flag a verb that is really there"
        );
    }

    /// The campaign is not merely named in the catalog: a generic host can drive it and recover
    /// the exact actor-bound state from its landed-move journal after a fresh-host restart.
    #[test]
    fn the_campaign_catalog_mount_drives_and_resumes_by_replay() {
        use dreggnet_offerings::{
            DreggIdentity, InMemoryResumeStore, Outcome, SessionConfig, SessionId,
        };

        let cfg = CatalogConfig::default();
        let store = InMemoryResumeStore::new();
        let id = SessionId::new("catalog-campaign-restart");
        let actor = DreggIdentity("catalog-campaign-player".to_string());

        let before = {
            let mut host = full_catalog_host(&cfg).with_resume_store(Box::new(store.clone()));
            assert_eq!(
                host.title(DescentCampaignOffering::KEY),
                Some(
                    "The Deepening Ways — player-driven native Descent expeditions; only a replay-verified Crown opens each real region road"
                )
            );
            host.open_session(
                DescentCampaignOffering::KEY,
                id.clone(),
                SessionConfig::with_seed(73),
            )
            .expect("the catalog campaign opens");
            let delve = host
                .actions_for(DescentCampaignOffering::KEY, &id, &actor)
                .expect("campaign actions")
                .into_iter()
                .find(|action| action.turn == "delve" && action.enabled)
                .expect("the player is offered a manual delve");
            assert!(matches!(
                host.advance(DescentCampaignOffering::KEY, &id, delve, actor.clone()),
                Some(Outcome::Landed { .. })
            ));
            let report = host
                .verify(DescentCampaignOffering::KEY, &id)
                .expect("campaign verifier is mounted");
            assert!(report.verified, "{}", report.detail);
            assert_eq!(report.turns, 2, "genesis plus the submitted delve");
            host.commitment(DescentCampaignOffering::KEY, &id)
                .expect("live campaign commitment")
        };

        let mut restarted = full_catalog_host(&cfg).with_resume_store(Box::new(store.clone()));
        let results = restarted.resume_all();
        assert_eq!(results.len(), 1, "one campaign log was persisted");
        assert!(results[0].1.is_ok(), "campaign log replays: {results:?}");
        assert_eq!(
            restarted.commitment(DescentCampaignOffering::KEY, &id),
            Some(before),
            "a fresh catalog host reconstructs the exact campaign head"
        );
        assert!(
            restarted
                .verify(DescentCampaignOffering::KEY, &id)
                .expect("resumed verifier")
                .verified
        );
    }
}
