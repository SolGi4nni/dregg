//! # `dreggnet-catalog` — the ONE statement of what the DreggNet offering catalog is.
//!
//! [`build_full_catalog`] registers the full 20-offering portfolio — the seven games
//! (native Descent · dungeon · council · market · Dark Bazaar · multiway-tug · automatafl), the eight do-once RPG
//! feature surfaces ([`dreggnet_surfaces::register_surfaces`]: trade · inventory · cheevos ·
//! guild · craft · companion · tavern · party), and the five service offerings (doc · names ·
//! compute · grain · hermes) — into a caller-supplied [`OfferingHost`]. Every frontend builds its
//! host through this one function, so "which offerings exist" stops being four hand-maintained
//! lists (`dreggnet_web::catalog_default_host` + `register_non_game_offerings`,
//! `dreggnet_telegram::host::telegram_default_host`, `dreggnet_wechat::host::wechat_default_host`,
//! and discord-bot's bespoke per-type stores) that can silently disagree.
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
//! tug board, or party — several identities acting on one object), and WRONG for the seven
//! identity-owned RPG feature surfaces. Mounted globally those seven give every viewer the SAME
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
use dreggnet_offerings::dungeon::DungeonOffering;
use dreggnet_offerings::native_descent::NativeDescentOffering;

use dregg_automatafl::AutomataflOffering;
use dreggnet_council::{CandidateProposal, CouncilOffering};
use dreggnet_market::{DarkBazaarOffering, MarketOffering};

pub mod player_worlds;
pub mod seated;

pub use player_worlds::{PlayerWorlds, RPG_KEYS, build_player_host, is_rpg_key};

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
}

/// **THE seam: register the full DreggNet portfolio into `host`.** Seven games + eight RPG
/// feature surfaces + five service offerings = the 20 every frontend exposes. Call it inside
/// the frontend's host-build closure (on the host's owning thread) so `!Send` offering
/// internals are born confined, exactly as the four per-frontend registrars do today.
pub fn build_full_catalog(host: &mut OfferingHost, cfg: &CatalogConfig) {
    register_games(host, cfg);
    register_feature_surfaces(host);
    register_services(host, cfg);
}

/// Build a fresh [`OfferingHost`] carrying the full catalog — the convenience every
/// `*_default_host` collapses into (`HostThread::spawn(move || full_catalog_host(&cfg))`).
pub fn full_catalog_host(cfg: &CatalogConfig) -> OfferingHost {
    let mut host = OfferingHost::new();
    build_full_catalog(&mut host, cfg);
    host
}

/// **The seven portfolio games** — native Descent · dungeon · council · market · Dark Bazaar ·
/// tug · automatafl.
/// Port source (titles + shapes, byte-identical across the three existing copies):
/// `dreggnet-web/src/lib.rs:1232-1282` / `dreggnet-telegram/src/host.rs:419-451`.
pub fn register_games(host: &mut OfferingHost, cfg: &CatalogConfig) {
    host.register(
        "descent",
        "The Descent — the Lean-authored custody dungeon (delve · unlock · smite · loot · bank)",
        NativeDescentOffering::new(),
    );
    host.register(
        "dungeon",
        "The Warden's Keep — a verifiable dungeon (offering #0)",
        DungeonOffering::new(),
    );
    host.register(
        "council",
        "DreggNet Council — propose · vote · enact",
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
        "The Dark Bazaar — playable CRAWL (sealed bids · verified settlement)",
        DarkBazaarOffering::new(),
    );
    // `tug` needs the seat-claiming adapter: `TugOffering` names its two seats by fixed
    // canonical strings while every frontend's user identity is a derived key, so the ONE
    // shared `seated::SeatedTug` (port of `dreggnet-web/src/seated.rs`, collapsing the
    // telegram/wechat/discord byte-peers) claims seats for the first two identities that act.
    host.register(
        "tug",
        "Multiway-Tug — a hidden-hand tug of influence (seven guilds · eight actions)",
        seated::SeatedTug::new(),
    );
    host.register(
        "automatafl",
        "Automatafl — the simultaneous-move board (seal a move · reveal · the automaton steps)",
        AutomataflOffering,
    );
}

/// **The eight do-once RPG feature surfaces** — trade · inventory · cheevos · guild · craft ·
/// companion · tavern · party, on ONE `SharedWorld` (so craft → inventory → trade compose over one
/// ledger).
///
/// ⚠ **ANONYMOUS / SINGLE-PLAYER ONLY.** The world this mounts belongs to
/// [`dreggnet_surfaces::DEMO_PLAYER`] and is shared by every session on the host, so on a host
/// serving more than one viewer *every player shares one inventory*. A frontend with identified
/// viewers routes the seven [`is_rpg_key`] keys to a per-identity host from [`PlayerWorlds`]
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
        "DreggNet Doc — a verifiable document store (author · amend · verify)",
        dreggnet_doc::DocOffering::new(),
    );
    host.register(
        "names",
        "DreggNet Names — an identity / naming service (register · transfer · resolve)",
        dreggnet_names::NamesOffering::new(),
    );
    host.register(
        "compute",
        "DreggNet Compute — a confined compute-job market (post · claim · settle)",
        dreggnet_compute::ComputeOffering::new(),
    );
    host.register(
        "grain",
        "DreggNet Grain — metered work under a spend budget (request · grant)",
        dreggnet_grain::GrainOffering::new(cfg.grain_budget),
    );
    host.register(
        "hermes",
        "DreggNet Hermes — the message relay (send · deliver · ack)",
        dreggnet_hermes::HermesOffering::new(),
    );
}

/// The 20 catalog keys, in registration order — the parity contract. Every frontend's
/// "which offerings exist" question resolves to this ONE list; the test below pins
/// `full_catalog_host` to it, and a frontend cutover test can pin its old registrar against
/// the same constant before deleting it.
pub const CATALOG_KEYS: [&str; 20] = [
    // games
    "descent",
    "dungeon",
    "council",
    "market",
    "bazaar",
    "tug",
    "automatafl",
    // feature surfaces (dreggnet_surfaces::register_surfaces order)
    "trade",
    "inventory",
    "cheevos",
    "guild",
    "craft",
    "companion",
    "tavern",
    "party",
    // services
    "doc",
    "names",
    "compute",
    "grain",
    "hermes",
];

// ─────────────────────────────────────────────────────────────────────────────
// THE LAB FRAMING — the one place the catalog's product words live
// ─────────────────────────────────────────────────────────────────────────────

/// **The Lab intro** — the honest framing every catalog LISTING leads with, on every front
/// door (web `GET /offerings`, the Mini App `/tg` fragment, Telegram `/offerings`, Discord
/// `/play`). The 20 offerings are the engine's proving ground — real verifiable turns,
/// deliberately rough — not the polished game. ONE string, so the three front doors cannot
/// drift into three different stories about what the catalog is.
pub fn lab_intro() -> &'static str {
    "🧪 The Lab — experimental engine surfaces. Everything here runs real, verifiable \
     turns on the dregg substrate; none of it is the polished game yet. These are the \
     parts the game is built from, on the shelf for the curious."
}

/// **The flagship pointer** — where the game begins. The Lean-authored Descent is registered in
/// the common catalog so web, Telegram, and Discord all drive the same rules; dedicated
/// `/descent` routes may provide richer presentation over that same core.
pub fn flagship_pointer() -> &'static str {
    "⚔️ The Descent — the Lean-authored custody dungeon. Delve under a finite light clock; \
     exercise attenuating keys; carry only what the descent permits; bank only on a proved exit."
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The parity contract: the full catalog registers exactly [`CATALOG_KEYS`] — the same 20
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
}
