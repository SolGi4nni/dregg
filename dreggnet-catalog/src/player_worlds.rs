//! # `PlayerWorlds` — **one persistent RPG world per derived identity**, in the shared layer.
//!
//! ## The defect this closes
//!
//! [`dreggnet_surfaces::register_surfaces`] mounts ONE `SharedWorld::demo("Adventurer")` per host,
//! and the surfaces key their shelves on that world's single canonical player. Mounted on a
//! frontend's ONE global host — which is exactly what the web and Telegram catalogs do — that
//! means **every viewer shares one inventory**: player A forges a Greatblade and it appears in
//! player B's inventory, listable on B's stall, because there is only one ledger and everybody is
//! "Adventurer".
//!
//! The Discord bot found this independently and fixed it with one `OfferingHost` per derived
//! identity (`discord-bot/src/commands/rpg_world.rs`'s `build_player_host` + its `HostMap`). That
//! fix never came back to the shared layer, so web and Telegram still carry the original bug. This
//! module IS that fix, lifted: the per-identity host construction lives here, so every frontend
//! keys a world by the viewer's identity with one call.
//!
//! ## The shape
//!
//! Isolation comes from the **host**, not from a label: each identity gets its own
//! [`OfferingHost`], with its own world, forge, `AssetWorld`, item registry and sessions. Nothing
//! crosses between them — there is no shared cell to leak through.
//!
//! ```ignore
//! let mut worlds = PlayerWorlds::new();                 // or ::with_store(|id| …) for durability
//! let host = worlds.host_mut(&viewer_identity_hex);     // built (and resumed) on first touch
//! host.ensure_open("craft", &SessionId::new("primary"))?;
//! ```
//!
//! ## Which offerings belong here
//!
//! The eight identity-owned RPG feature surfaces ([`RPG_KEYS`]) and ONLY those. They are per-player
//! by nature (an inventory is yours). The nine games, `party`, and five service offerings in
//! [`crate::build_full_catalog`] are shared tables — a council with one voter per host is not a
//! council, and a party with one role per private host is not a party — so a frontend keeps routing
//! those to its one global host and routes [`is_rpg_key`] keys here.
//!
//! ## Durability
//!
//! A per-identity host is only as durable as its store. [`PlayerWorlds::with_store`] takes a
//! factory `identity -> Option<Box<dyn SessionResumeStore>>`; the host is built with that store
//! attached and then **boot-resumed by replay** ([`OfferingHost::resume_all`], which since the
//! ordered-replay fix re-drives order-dependent logs in a dependency-respecting order rather than
//! the store's arbitrary enumeration order). A store that refuses to re-drive leaves its session
//! closed and its record kept — fail-closed, never reopened to a forged state.

use std::collections::HashMap;

use dreggnet_offerings::OfferingHost;
use dreggnet_offerings::resume::SessionResumeStore;

/// **The eight identity-owned RPG surface keys** — the offerings a [`PlayerWorlds`] host mounts.
/// `party` is intentionally NOT here: it is a multi-identity lobby and therefore stays on the
/// shared catalog host.
pub const RPG_KEYS: [&str; 8] = [
    "trade",
    "inventory",
    "cheevos",
    "guild",
    "craft",
    "companion",
    "quest",
    "tavern",
];

/// Whether `key` is one of the eight per-player RPG surfaces (routed to a [`PlayerWorlds`] host
/// rather than the frontend's shared catalog host).
pub fn is_rpg_key(key: &str) -> bool {
    RPG_KEYS.contains(&key)
}

/// How a per-identity host gets its durable [`SessionResumeStore`] — `identity -> store`. `None`
/// means "no durable store for this identity" (the world lives only in memory).
type StoreFactory = dyn Fn(&str) -> Option<Box<dyn SessionResumeStore>>;

/// A hook run on a freshly-built per-identity host, after the surfaces are registered and BEFORE
/// its persisted sessions are replayed — the seam a frontend uses to replace a demo-fixture
/// surface with the player's real state (Discord re-registers `cheevos` with the player's own
/// earned proofs here).
type Customizer = dyn Fn(&mut OfferingHost, &str);

/// **One persistent RPG world per derived identity.** Hosts are built lazily on first touch
/// ([`host_mut`](PlayerWorlds::host_mut)) and cached; each is an independent
/// [`OfferingHost`] carrying the eight [`RPG_KEYS`] surfaces on its own world.
///
/// Not `Send` — an [`OfferingHost`] holds `!Send` `Rc`-backed sessions, so a frontend confines a
/// `PlayerWorlds` to one owning thread exactly as it already confines its catalog host (the web /
/// Telegram `HostThread`, Discord's `rpg-worlds` thread).
#[derive(Default)]
pub struct PlayerWorlds {
    hosts: HashMap<String, OfferingHost>,
    store_factory: Option<Box<StoreFactory>>,
    customize: Option<Box<Customizer>>,
}

impl PlayerWorlds {
    /// A registry whose per-identity hosts are **in-memory only** (no durable store): each world
    /// is real and isolated, but does not survive a restart.
    pub fn new() -> Self {
        PlayerWorlds::default()
    }

    /// A registry whose per-identity hosts each attach the store `factory` mints for that identity
    /// — the durable path. A host built with a store is boot-resumed by replay immediately.
    ///
    /// The factory MUST scope the store to the identity it is called with (one directory / one
    /// row-set per player): the whole isolation guarantee rests on no identity's host ever seeing
    /// another's logs.
    pub fn with_store(
        factory: impl Fn(&str) -> Option<Box<dyn SessionResumeStore>> + 'static,
    ) -> Self {
        PlayerWorlds {
            store_factory: Some(Box::new(factory)),
            ..PlayerWorlds::default()
        }
    }

    /// Attach a [`Customizer`] run on each freshly-built host (after registration, before replay)
    /// — where a frontend swaps a demo-fixture surface for the player's real one.
    pub fn with_customizer(
        mut self,
        customize: impl Fn(&mut OfferingHost, &str) + 'static,
    ) -> Self {
        self.customize = Some(Box::new(customize));
        self
    }

    /// **`identity`'s own host**, built on first touch. The build is the lift of Discord's
    /// `build_player_host`: register the eight identity-owned surfaces on a world seeded for
    /// `identity`, run the customizer, then reopen every persisted session by replay.
    pub fn host_mut(&mut self, identity: &str) -> &mut OfferingHost {
        if !self.hosts.contains_key(identity) {
            let store = self.store_factory.as_ref().and_then(|f| f(identity));
            let host = build_player_host(identity, store, self.customize.as_deref());
            self.hosts.insert(identity.to_string(), host);
        }
        self.hosts
            .get_mut(identity)
            .expect("the host was just inserted")
    }

    /// `identity`'s host if it is already built (no build-on-touch) — a read for a frontend that
    /// wants to answer "is this player's world live?" without materializing one.
    pub fn get(&self, identity: &str) -> Option<&OfferingHost> {
        self.hosts.get(identity)
    }

    /// **Drop `identity`'s in-memory host.** Their durable logs stay: the next touch rebuilds the
    /// world by replay — the same path a process restart takes. The eviction lever a long-running
    /// frontend needs so idle players do not pin memory forever.
    pub fn evict(&mut self, identity: &str) -> bool {
        self.hosts.remove(identity).is_some()
    }

    /// How many identities currently have a live in-memory host.
    pub fn len(&self) -> usize {
        self.hosts.len()
    }

    /// Whether no identity has a live host yet.
    pub fn is_empty(&self) -> bool {
        self.hosts.is_empty()
    }
}

/// **Build ONE identity's persistent RPG host** — the shared-layer form of Discord's
/// `build_player_host`.
///
/// 1. Mount the eight identity-owned surfaces on a [`dreggnet_surfaces::SharedWorld`] seeded for
///    `identity` (`dreggnet_surfaces::register_player_surfaces_for`), so craft / inventory / trade
///    compose over ONE ledger that belongs to this player and nobody else.
/// 2. Run `customize` (a frontend replacing a demo-fixture surface with the player's real state).
/// 3. Attach `store` and boot-resume every persisted session by REPLAY
///    ([`OfferingHost::resume_all`]) — in dependency-respecting order, so a `trade` log recorded
///    against a note the `craft` log minted re-drives after it rather than being refused.
///
/// A log that genuinely refuses to re-drive leaves its session closed and its durable record kept
/// (fail-closed); the built host is returned regardless, so one dead session never denies a player
/// their world.
pub fn build_player_host(
    identity: &str,
    store: Option<Box<dyn SessionResumeStore>>,
    customize: Option<&Customizer>,
) -> OfferingHost {
    let mut host = OfferingHost::new();
    if let Some(store) = store {
        host = host.with_resume_store(store);
    }
    dreggnet_surfaces::register_player_surfaces_for(&mut host, identity);
    if let Some(customize) = customize {
        customize(&mut host, identity);
    }
    // Replay whatever this identity persisted. `resume_all` orders the logs itself (the
    // dependency-respecting fixpoint in `OfferingHost::resume_logs`), so no caller has to know
    // that craft mints for trade.
    let _ = host.resume_all();
    host
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::resume::InMemoryResumeStore;
    use dreggnet_offerings::{Action, DreggIdentity, SessionId};

    fn primary() -> SessionId {
        SessionId::new("primary")
    }

    fn mover() -> DreggIdentity {
        DreggIdentity("driver".to_string())
    }

    fn rendered(host: &OfferingHost, key: &str) -> String {
        format!(
            "{:?}",
            host.render(key, &primary())
                .unwrap_or_else(|| panic!("`{key}` renders"))
                .view()
        )
    }

    /// Forge the safe Greatblade (bench recipe 0) as one real landed turn.
    fn craft_greatblade(host: &mut OfferingHost) {
        host.ensure_open("craft", &primary()).expect("craft opens");
        let out = host
            .advance(
                "craft",
                &primary(),
                Action::new("Forge Greatblade", "craft", 0, true),
                mover(),
            )
            .expect("craft session live");
        assert!(out.landed(), "the greatblade craft lands: {out:?}");
    }

    /// Every per-identity host carries exactly the eight identity-owned RPG keys. The party stays
    /// on the global host so several identities can inhabit one lobby.
    #[test]
    fn a_player_host_mounts_only_the_eight_identity_owned_rpg_surfaces() {
        let mut worlds = PlayerWorlds::new();
        let host = worlds.host_mut("alice");
        for key in RPG_KEYS {
            assert!(host.has(key), "`{key}` is mounted on the player host");
            assert!(is_rpg_key(key));
        }
        assert!(
            !host.has("party"),
            "a private player host must not contain a party lobby"
        );
        assert!(
            !is_rpg_key("party"),
            "party routes to the shared catalog host"
        );
        assert!(!is_rpg_key("council"), "a shared table is not per-player");
    }

    /// The routing decision itself is pure and cheap to pin: party shares the same host as other
    /// multi-identity tables, while all eight identity-owned features remain private.
    #[test]
    fn party_routes_shared_while_identity_owned_surfaces_route_private() {
        assert_eq!(RPG_KEYS.len(), 8);
        assert!(RPG_KEYS.into_iter().all(is_rpg_key));
        assert!(!is_rpg_key("party"));
        assert!(!is_rpg_key("council"));
    }

    /// **THE ISOLATION FALSIFIER** — the defect this module exists to close. Alice forges an item;
    /// it is on HER shelf and listable on HER stall, and Bob's inventory does not hold it. Under
    /// the single `register_surfaces` demo world every frontend mounted, it did.
    #[test]
    fn two_identities_worlds_are_isolated() {
        let mut worlds = PlayerWorlds::new();

        let alice_host = worlds.host_mut("alice");
        craft_greatblade(alice_host);
        alice_host
            .ensure_open("inventory", &primary())
            .expect("alice's inventory opens");
        let alice = rendered(alice_host, "inventory");
        assert!(
            alice.contains("Greatblade"),
            "alice's own forge lands on her own shelf: {alice}"
        );

        let bob_host = worlds.host_mut("bob");
        bob_host
            .ensure_open("inventory", &primary())
            .expect("bob's inventory opens");
        bob_host
            .ensure_open("trade", &primary())
            .expect("bob's stall opens");
        // Non-vacuous: bob's stall really does offer listings — just none of alice's.
        assert!(
            !bob_host
                .actions("trade", &primary())
                .expect("bob's stall is live")
                .is_empty(),
            "bob has his own seeded stock to list"
        );
        let bob = rendered(bob_host, "inventory");
        assert!(
            !bob.contains("Greatblade"),
            "bob's inventory holds no note alice forged: {bob}"
        );
        assert!(
            !bob_host
                .actions("trade", &primary())
                .expect("bob's stall is live")
                .iter()
                .any(|a| a.label.contains("Greatblade")),
            "bob cannot list a note alice forged"
        );
        assert_eq!(worlds.len(), 2, "two identities, two hosts");
    }

    /// A durable per-identity world survives a restart: a fresh `PlayerWorlds` over the SAME
    /// per-identity stores replays each world back, and the isolation holds across the replay
    /// (alice's crafted note reopens on her shelf; bob's world is still empty of it).
    #[test]
    fn per_identity_worlds_survive_a_restart_by_replay_and_stay_isolated() {
        let alice_store = InMemoryResumeStore::new();
        let bob_store = InMemoryResumeStore::new();
        let factory = {
            let a = alice_store.clone();
            let b = bob_store.clone();
            move |identity: &str| -> Option<Box<dyn SessionResumeStore>> {
                match identity {
                    "alice" => Some(Box::new(a.clone())),
                    "bob" => Some(Box::new(b.clone())),
                    _ => None,
                }
            }
        };

        {
            let mut worlds = PlayerWorlds::with_store(factory.clone());
            let alice = worlds.host_mut("alice");
            craft_greatblade(alice);
            // …and LIST it, so the restart has an order-dependent pair of logs to replay
            // (the trade listing only re-drives after the craft that minted the note).
            alice.ensure_open("trade", &primary()).expect("trade opens");
            let list = alice
                .actions("trade", &primary())
                .expect("live")
                .into_iter()
                .find(|a| a.turn == "list" && a.label.contains("Greatblade"))
                .expect("the crafted note is listable");
            assert!(
                alice
                    .advance("trade", &primary(), list, mover())
                    .expect("live")
                    .landed(),
                "the listing lands"
            );
            let _ = worlds.host_mut("bob").ensure_open("inventory", &primary());
        }

        // "Restart": brand-new registry, same per-identity stores.
        let mut worlds = PlayerWorlds::with_store(factory);
        let alice = worlds.host_mut("alice");
        assert!(alice.is_open("craft", &primary()), "alice's craft resumed");
        assert!(alice.is_open("trade", &primary()), "alice's trade resumed");
        assert!(
            alice.verify("craft", &primary()).expect("live").verified,
            "the resumed craft chain re-verifies"
        );
        assert!(
            rendered(alice, "trade").contains("Greatblade"),
            "the crafted + listed note survived the restart"
        );

        let bob = worlds.host_mut("bob");
        bob.ensure_open("inventory", &primary()).expect("opens");
        assert!(
            !rendered(bob, "inventory").contains("Greatblade"),
            "bob's replayed world is still disjoint from alice's"
        );
    }

    /// Eviction drops only the in-memory host: the durable logs stay, so the next touch rebuilds
    /// the SAME world by replay (the process-restart path, exercised in-process).
    #[test]
    fn evicting_a_host_rebuilds_the_same_world_on_the_next_touch() {
        let store = InMemoryResumeStore::new();
        let mut worlds = PlayerWorlds::with_store({
            let s = store.clone();
            move |identity: &str| -> Option<Box<dyn SessionResumeStore>> {
                (identity == "alice").then(|| Box::new(s.clone()) as Box<dyn SessionResumeStore>)
            }
        });
        craft_greatblade(worlds.host_mut("alice"));
        assert!(worlds.evict("alice"), "the live host is dropped");
        assert_eq!(worlds.len(), 0);
        assert!(worlds.get("alice").is_none());

        let rebuilt = worlds.host_mut("alice");
        assert!(rebuilt.is_open("craft", &primary()), "rebuilt by replay");
        rebuilt
            .ensure_open("inventory", &primary())
            .expect("inventory opens over the replayed world");
        assert!(rendered(rebuilt, "inventory").contains("Greatblade"));
    }

    /// The customizer runs on a freshly-built host and can replace a mounted surface — the seam
    /// Discord uses to swap the demo cheevo showcase for the player's real earned proofs.
    #[test]
    fn the_customizer_can_replace_a_mounted_surface() {
        let mut worlds = PlayerWorlds::new().with_customizer(|host, _identity| {
            host.register(
                "cheevos",
                "Achievements — earned soulbound proofs over verified runs",
                dreggnet_surfaces::CheevoShowcase::empty(),
            );
        });
        let host = worlds.host_mut("carol");
        host.ensure_open("cheevos", &primary()).expect("opens");
        let text = rendered(host, "cheevos");
        assert!(
            !text.contains("Ada"),
            "the demo fixture's earner is gone from a customized showcase: {text}"
        );
    }
}
