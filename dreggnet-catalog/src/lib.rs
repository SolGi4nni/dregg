//! # `dreggnet-catalog` — the ONE statement of what the DreggNet offering catalog is.
//!
//! [`build_full_catalog`] registers the full 18-offering portfolio — the five games
//! (dungeon · council · market · multiway-tug · automatafl), the eight do-once RPG feature
//! surfaces ([`dreggnet_surfaces::register_surfaces`]: trade · inventory · cheevos · guild ·
//! craft · companion · tavern · party), and the five service offerings (doc · names · compute ·
//! grain · hermes) — into a caller-supplied [`OfferingHost`]. Every frontend builds its host
//! through this one function, so "which offerings exist" stops being four hand-maintained lists
//! (`dreggnet_web::catalog_default_host` + `register_non_game_offerings`,
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
//! ## State (Phase A + B-for-Telegram of docs/BOT-SHARED-BACKEND-DESIGN.md)
//! The registrars are complete ports of the (byte-identical) web/telegram registrations, and the
//! [`seated`] adapter is the complete port of `dreggnet-web/src/seated.rs` (the source of the four
//! byte-peers). `dreggnet-telegram` builds its host through [`full_catalog_host`] and re-exports
//! [`seated::SeatedTug`]; web/wechat delegation and Discord's cutover onto `OfferingHost` are the
//! design doc's Phases B (rest) and C.

use dreggnet_offerings::OfferingHost;
use dreggnet_offerings::dungeon::DungeonOffering;

use dregg_automatafl::AutomataflOffering;
use dreggnet_council::{CandidateProposal, CouncilOffering};
use dreggnet_market::MarketOffering;

pub mod seated;

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

/// **THE seam: register the full DreggNet portfolio into `host`.** Five games + eight RPG
/// feature surfaces + five service offerings = the 18 every frontend exposes. Call it inside
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

/// **The five portfolio games** — dungeon · council · market · tug · automatafl.
/// Port source (titles + shapes, byte-identical across the three existing copies):
/// `dreggnet-web/src/lib.rs:1232-1282` / `dreggnet-telegram/src/host.rs:419-451`.
pub fn register_games(host: &mut OfferingHost, cfg: &CatalogConfig) {
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
/// companion · tavern · party. This delegation IS the already-shared registrar
/// (`dreggnet-surfaces/src/lib.rs:166`): it mounts ONE `SharedWorld` across
/// trade/inventory/craft, which is exactly the composition Discord's per-open
/// `SharedWorld::demo(…)` stores sever today (`discord-bot/src/commands/portfolio.rs:403`).
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

/// The 18 catalog keys, in registration order — the parity contract. Every frontend's
/// "which offerings exist" question resolves to this ONE list; the test below pins
/// `full_catalog_host` to it, and a frontend cutover test can pin its old registrar against
/// the same constant before deleting it.
pub const CATALOG_KEYS: [&str; 18] = [
    // games
    "dungeon",
    "council",
    "market",
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The parity contract: the full catalog registers exactly [`CATALOG_KEYS`] — the same 18
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
