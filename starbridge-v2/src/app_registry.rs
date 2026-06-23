//! THE APP REGISTRY — pre-built starbridge-apps wired into the live cockpit.
//!
//! The census (`docs/deos/APP-AND-FEDERATION-CENSUS-2026-06-23.md`) found the
//! chasm: `dregg-app-framework` is real + load-bearing and the 20 starbridge-apps
//! are fully built + tested — but `starbridge-v2` did not even depend on them.
//! There was no `AppRegistry`, no launcher, no way to open a *pre-built* app. The
//! powerbox (`crate::powerbox`) can birth a *bare* confined cell; it cannot open a
//! gallery/tussle/auction.
//!
//! This module closes that gap by INTEGRATION (the framework + apps already exist):
//! an [`AppRegistry`] lists each wired app — its id, name, what-it-does, and the
//! real `*_app(cipherclerk, executor) -> DeosApp` ctor — and [`AppRegistry::launch`]
//! instantiates an entry against a **live app-substrate** ([`AppSubstrate`]: an
//! [`AppCipherclerk`] + [`EmbeddedExecutor`] from the app framework), seeds the
//! app's backing cell so its program bites, and returns a [`LaunchedRegistryApp`]
//! whose affordances fire **REAL verified turns** on that substrate's ledger.
//!
//! ## What "the live World" means here (honest)
//!
//! The cockpit's [`crate::world::World`] wraps `dregg_sdk::embed::DreggEngine`,
//! which owns its `dregg_cell::Ledger` BY VALUE. The app framework's
//! [`EmbeddedExecutor`] wraps an `AgentRuntime` whose ledger is an
//! `Arc<Mutex<Ledger>>`. They are DISTINCT physical ledgers — folding an app's
//! cells into `World`'s engine ledger would need a `World`/`DreggEngine` refactor
//! out of this lane's scope. So a launched app runs on its OWN app-substrate
//! ledger (the app framework's), NOT `World`'s engine ledger.
//!
//! What IS genuinely shared — and what the verify test proves — is the substrate
//! ledger BETWEEN the fire and the inspector: a launched app's affordance fire
//! WRITES to the substrate's executor ledger, and a second reader of that SAME
//! executor ([`AppSubstrate::cell_state`]) sees the new cell state. That is a real
//! shared ledger (writer = the verified turn; reader = the inspector seam), just
//! the app-framework's ledger rather than `World`'s. The registry is the cockpit's
//! own holder of these app substrates, so the cockpit's app-inspector reads them.
//!
//! gpui-free and `cargo test`-able (gated on `app-registry`, pulled by
//! `embedded-executor`): the launch + the real verified turn run with no GPU.

use dregg_app_framework::{
    AppCipherclerk, AuthRequired, DeosApp, EmbeddedExecutor, FireExecuteError, TurnReceipt,
};
use dregg_sdk::AgentCipherclerk;
use dregg_types::CellId;

#[cfg(feature = "embedded-executor")]
use crate::app_worldspine::{default_domain_token, AppWorldSpine, SeedField, WorldFireError};
#[cfg(feature = "embedded-executor")]
use crate::world::World;
#[cfg(feature = "embedded-executor")]
use std::cell::RefCell;
#[cfg(feature = "embedded-executor")]
use std::rc::Rc;

/// One **app substrate** — an [`AppCipherclerk`] + [`EmbeddedExecutor`] pair (the
/// app framework's SDK surface every verified-turn fire routes through). A launched
/// registry app owns one; its backing cell, its seeded program, and every turn it
/// fires live on this substrate's verified ledger.
///
/// The substrate's executor ledger is the SHARED ledger the inspector reads: a fire
/// writes to it, [`AppSubstrate::cell_state`] reads it back (the same `Ledger`
/// behind the `EmbeddedExecutor`'s `Arc<Mutex<Ledger>>`).
#[derive(Clone)]
pub struct AppSubstrate {
    cipherclerk: AppCipherclerk,
    executor: EmbeddedExecutor,
}

impl AppSubstrate {
    /// Build a fresh app substrate over a fresh SDK cipherclerk, in `federation`.
    ///
    /// Each launched app gets its OWN substrate: gallery / sealed-auction /
    /// bounty-board all back their primary cell on the executor's OWN cell
    /// (`cipherclerk.cell_id()`), so two apps on one shared executor would collide
    /// on that cell. A per-app substrate keeps each app's cell + ledger distinct
    /// while still being a REAL verified ledger the inspector can read.
    pub fn new(federation: [u8; 32]) -> Self {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), federation);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        AppSubstrate {
            cipherclerk: cclerk,
            executor,
        }
    }

    /// The signing handle (the app framework's narrow cipherclerk).
    pub fn cipherclerk(&self) -> &AppCipherclerk {
        &self.cipherclerk
    }

    /// The turn-submission handle (the embedded verified executor + ledger).
    pub fn executor(&self) -> &EmbeddedExecutor {
        &self.executor
    }

    /// The substrate's primary cell id (the agent's own cell — the cell most apps
    /// back their state on).
    pub fn cell_id(&self) -> CellId {
        self.executor.cell_id()
    }

    /// The **live state** of `cell` on the substrate's ledger, if present — the
    /// inspector read. This is the SAME ledger an affordance fire wrote to, so a
    /// post-fire read sees the new state (the shared-ledger tooth).
    pub fn cell_state(&self, cell: CellId) -> Option<dregg_cell::state::CellState> {
        self.executor.cell_state(cell)
    }
}

/// A **launched registry app** — a pre-built [`DeosApp`] instantiated over a live
/// [`AppSubstrate`], with its backing cell seeded so its program bites. Its
/// affordances fire REAL verified turns (via [`Self::drive`]); its cell + state are
/// visible to a second reader of the substrate ([`AppSubstrate::cell_state`]).
pub struct LaunchedRegistryApp {
    /// The registry id of the app that was launched (e.g. `"gallery"`).
    pub id: &'static str,
    /// The composed deos app (cells × affordances over the substrate).
    pub app: DeosApp,
    /// The live substrate the app runs on (the shared verified ledger).
    pub substrate: AppSubstrate,
    /// How to fire ONE representative affordance of this app — a real verified turn
    /// that lands a [`TurnReceipt`] AND advances the backing cell's state, so the
    /// launch is proven by RUNNING, not by construction. Carried per-entry because
    /// each app's lifecycle is different (gallery `submit`, auction `commit_bid`,
    /// …).
    drive: DriveFn,
}

impl LaunchedRegistryApp {
    /// The backing (primary) cell of the launched app — what the inspector points at.
    pub fn primary_cell(&self) -> CellId {
        self.substrate.cell_id()
    }

    /// **Drive one representative affordance** — fire a real verified turn on the
    /// live substrate. Returns the executor's OWN [`TurnReceipt`] (the proof the
    /// turn committed). The fire WRITES to the substrate ledger; read the new state
    /// back with [`AppSubstrate::cell_state`] (the inspector seam) to confirm the
    /// shared ledger.
    pub fn drive(&self) -> Result<TurnReceipt, FireExecuteError> {
        (self.drive)(&self.app, &self.substrate)
    }
}

/// The per-app drive closure — fires one representative affordance through the
/// substrate's cipherclerk + executor.
type DriveFn = fn(&DeosApp, &AppSubstrate) -> Result<TurnReceipt, FireExecuteError>;

/// The per-app **World drive** closure — seed the app's cell onto the cockpit's LIVE
/// [`World`] and commit one representative affordance THROUGH it (`World::turn` →
/// `World::commit_turn`), so the app's cell + receipt land on `World::ledger()` /
/// `World::receipts()` (the cockpit inspector path), NOT the framework side-ledger.
///
/// Receives the launched [`DeosApp`] (for its cap rights + the app cell) and the
/// shared `World`. Returns the [`AppWorldSpine`] (already seeded, app cell installed)
/// + the committed [`TurnReceipt`]. The closure uses the app crate's OWN public
/// effect-builders + program, so the World path re-expresses the SAME turn the
/// framework path fires — only the ledger is the cockpit's now.
#[cfg(feature = "embedded-executor")]
type WorldDriveFn =
    fn(&DeosApp, Rc<RefCell<World>>) -> Result<(AppWorldSpine, TurnReceipt), WorldFireError>;

/// The per-app ctor — builds the [`DeosApp`] over a substrate.
type CtorFn = fn(&AppCipherclerk, &EmbeddedExecutor) -> DeosApp;

/// The per-app seed closure — installs the backing cell's program + genesis state
/// on the substrate so the app's gated fires have a live state and the executor
/// re-enforces the program.
type SeedFn = fn(&EmbeddedExecutor, &AppCipherclerk);

/// **One entry in the app registry** — a pre-built starbridge-app the cockpit can
/// launch. Names the app (id / display name / one-line description) and carries the
/// REAL ctor + seed + drive so a launch is wiring, not re-implementation.
#[derive(Clone, Copy)]
pub struct AppEntry {
    /// A stable, short id (the launch key / palette token), e.g. `"gallery"`.
    pub id: &'static str,
    /// The display name shown in the launcher list.
    pub name: &'static str,
    /// A one-line description of what the app does (what the user reads before
    /// launching).
    pub description: &'static str,
    /// The real `*_app(cipherclerk, executor) -> DeosApp` ctor.
    ctor: CtorFn,
    /// Seed the backing cell's program + genesis state on the substrate.
    seed: SeedFn,
    /// Fire one representative affordance (a real verified turn) — the proof.
    drive: DriveFn,
    /// Seed the app's cell onto the cockpit's LIVE [`World`] and commit one
    /// representative affordance THROUGH it — so the app's cell + receipt show in
    /// the cockpit's OWN inspector (`World::ledger()`/`receipts()`), not the
    /// framework side-ledger. This is the shared-ledger seam the editor lane's
    /// `WorldSpine` established, brought to launched apps. Gated on
    /// `embedded-executor` (it carries `World` types); the registry's framework-only
    /// build (`app-registry` without `embedded-executor`) omits this field.
    #[cfg(feature = "embedded-executor")]
    world_drive: WorldDriveFn,
}

impl AppEntry {
    /// **Launch this app** — build a fresh live [`AppSubstrate`] in `federation`,
    /// instantiate the [`DeosApp`] over it, seed the backing cell so its program
    /// bites, and return the [`LaunchedRegistryApp`]. The app's affordances now fire
    /// REAL verified turns on the substrate ledger (drive them with
    /// [`LaunchedRegistryApp::drive`]); its cell + state are visible to a second
    /// reader of the substrate.
    pub fn launch(&self, federation: [u8; 32]) -> LaunchedRegistryApp {
        let substrate = AppSubstrate::new(federation);
        let app = (self.ctor)(substrate.cipherclerk(), substrate.executor());
        (self.seed)(substrate.executor(), substrate.cipherclerk());
        LaunchedRegistryApp {
            id: self.id,
            app,
            substrate,
            drive: self.drive,
        }
    }

    /// **Launch this app ONTO the cockpit's LIVE [`World`]** — the shared-ledger seam.
    ///
    /// Builds the [`DeosApp`] over a fresh framework substrate (the cipherclerk is the
    /// app's identity), then SEEDS the app's primary cell + program + genesis state
    /// onto `world` and COMMITS one representative affordance through `World::turn` →
    /// `World::commit_turn`. The result: the app's cell + its receipt are on
    /// `World::ledger()` / `World::receipts()` — the SAME reads the cockpit's cell
    /// inspector makes. This is the editor lane's `WorldSpine` pattern brought to a
    /// launched app: the app's turns are now in the cockpit's own world, not a side
    /// ledger.
    ///
    /// Returns the seeded [`AppWorldSpine`] (so the host can fire MORE affordances onto
    /// `World`) + the first committed receipt.
    #[cfg(feature = "embedded-executor")]
    pub fn launch_on_world(
        &self,
        federation: [u8; 32],
        world: Rc<RefCell<World>>,
    ) -> Result<LaunchedOnWorld, WorldFireError> {
        let substrate = AppSubstrate::new(federation);
        let app = (self.ctor)(substrate.cipherclerk(), substrate.executor());
        let (spine, receipt) = (self.world_drive)(&app, world)?;
        Ok(LaunchedOnWorld {
            id: self.id,
            app,
            spine,
            receipt,
        })
    }
}

/// A **launched-on-World app** — a [`DeosApp`] whose primary cell + first affordance
/// receipt live on the cockpit's LIVE [`World`] ledger (the inspector path), via the
/// [`AppWorldSpine`] bridge. Distinct from [`LaunchedRegistryApp`] (which runs on the
/// framework's side-ledger): THIS one's cells + receipts are in the cockpit's own
/// world. Gated on `embedded-executor` (it carries `World`-side types).
#[cfg(feature = "embedded-executor")]
pub struct LaunchedOnWorld {
    /// The registry id of the app launched (e.g. `"gallery"`).
    pub id: &'static str,
    /// The composed deos app (cells × affordances).
    pub app: DeosApp,
    /// The seeded World bridge — the app cell is installed on `World`; fire MORE
    /// affordances onto the live world with [`AppWorldSpine::commit`].
    pub spine: AppWorldSpine,
    /// The first affordance's receipt — committed through `World::commit_turn`, now
    /// present in `World::receipts()`.
    pub receipt: TurnReceipt,
}

#[cfg(feature = "embedded-executor")]
impl LaunchedOnWorld {
    /// The app's primary cell on the World ledger (the inspector's pointer).
    pub fn primary_cell(&self) -> CellId {
        self.spine.app_cell()
    }
}

/// **The cockpit's app registry** — the list of pre-built starbridge-apps wired
/// into the live image. [`AppRegistry::standard`] is the starter set; launch an
/// entry with [`AppEntry::launch`] (or [`AppRegistry::launch`] by id).
#[derive(Clone)]
pub struct AppRegistry {
    entries: Vec<AppEntry>,
}

impl Default for AppRegistry {
    fn default() -> Self {
        Self::standard()
    }
}

impl AppRegistry {
    /// The **standard** starter set: the pre-built starbridge-apps that build
    /// cleanly over the embedded executor (gallery / tussle / sealed-auction /
    /// bounty-board). Each carries its real ctor + seed + a representative-fire
    /// drive. (Apps needing server/HTTP-only deps that don't fit the embedded build
    /// are left out — these four are pure cell/affordance apps over the framework.)
    pub fn standard() -> Self {
        AppRegistry {
            entries: vec![
                AppEntry {
                    id: "gallery",
                    name: "Sealed Gallery",
                    description:
                        "A juried art gallery with sealed (commit-reveal) submissions — \
                         artists commit, the curator closes, artists reveal, the curator features.",
                    ctor: starbridge_gallery::gallery_app,
                    seed: |exec, _cclerk| {
                        starbridge_gallery::seed_gallery(exec, "curator");
                    },
                    drive: |app, sub| {
                        // An ARTIST seals a submission in the SUBMISSION phase — a real
                        // verified turn writing the next free WriteOnce submission slot.
                        starbridge_gallery::fire_submit(
                            app,
                            &starbridge_gallery::ARTIST_RIGHTS,
                            dregg_app_framework::field_from_u64(0xA17),
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    #[cfg(feature = "embedded-executor")]
                    world_drive: |app, world| {
                        use starbridge_gallery as g;
                        // SEED the gallery cell onto the live World: the program (so World
                        // re-enforces the WriteOnce board + phase invariants) + the genesis
                        // baseline `seed_gallery` lays (curator bound, PHASE = SUBMISSION).
                        let app_cell = app.cells()[0].cell();
                        let spine = AppWorldSpine::seed(
                            world,
                            app_cell,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            g::gallery_program(),
                            &[
                                SeedField {
                                    slot: g::CURATOR_SLOT,
                                    value: dregg_app_framework::field_from_bytes(b"curator"),
                                },
                                SeedField {
                                    slot: g::PHASE_SLOT,
                                    value: dregg_app_framework::field_from_u64(g::PHASE_SUBMISSION),
                                },
                            ],
                        );
                        // COMMIT `submit` through World: the next free WriteOnce slot is read
                        // from World's LIVE state (exactly as `fire_submit` reads the
                        // framework state), so the submission lands on World's ledger.
                        let seal = dregg_app_framework::field_from_u64(0xA17);
                        let receipt = spine.commit(
                            "submit",
                            &g::ARTIST_RIGHTS,
                            &g::ARTIST_RIGHTS,
                            |live| {
                                let slot = g::next_free_submit_slot(live)
                                    .unwrap_or_else(|| g::submit_slot(0));
                                g::submit_effects(app_cell, slot, &seal)
                            },
                        )?;
                        Ok((spine, receipt))
                    },
                },
                AppEntry {
                    id: "sealed-auction",
                    name: "Sealed Auction",
                    description:
                        "A sealed-bid (commit-reveal) auction — bidders commit hashed bids, \
                         the seller closes commits, bidders reveal, the seller resolves the winner.",
                    ctor: starbridge_sealed_auction::auction_app,
                    seed: |exec, _cclerk| {
                        starbridge_sealed_auction::seed_auction(exec, "seller");
                    },
                    drive: |app, sub| {
                        // A BIDDER commits a sealed bid in the COMMIT phase.
                        starbridge_sealed_auction::fire_commit_bid(
                            app,
                            &starbridge_sealed_auction::BIDDER_RIGHTS,
                            dregg_app_framework::field_from_u64(0xB1D),
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    #[cfg(feature = "embedded-executor")]
                    world_drive: |app, world| {
                        use starbridge_sealed_auction as a;
                        let app_cell = app.cells()[0].cell();
                        // SEED onto World: program + `seed_auction` baseline (seller bound,
                        // PHASE = COMMIT).
                        let spine = AppWorldSpine::seed(
                            world,
                            app_cell,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            a::auction_program(),
                            &[
                                SeedField {
                                    slot: a::SELLER_SLOT,
                                    value: dregg_app_framework::field_from_bytes(b"seller"),
                                },
                                SeedField {
                                    slot: a::PHASE_SLOT,
                                    value: dregg_app_framework::field_from_u64(a::PHASE_COMMIT),
                                },
                            ],
                        );
                        // COMMIT `commit_bid` through World: next free WriteOnce commit slot
                        // read from World's live state.
                        let seal = dregg_app_framework::field_from_u64(0xB1D);
                        let receipt = spine.commit(
                            "commit_bid",
                            &a::BIDDER_RIGHTS,
                            &a::BIDDER_RIGHTS,
                            |live| {
                                let slot = a::next_free_commit_slot(live)
                                    .unwrap_or_else(|| a::commit_slot(0));
                                a::commit_bid_effects(app_cell, slot, &seal)
                            },
                        )?;
                        Ok((spine, receipt))
                    },
                },
                AppEntry {
                    id: "bounty-board",
                    name: "Bounty Board",
                    description:
                        "A bounty with an escrowed reward — a worker claims it, submits work, \
                         and the poster pays out (each step a cap-gated state-machine turn).",
                    ctor: starbridge_bounty_board::bounty_app,
                    seed: |exec, _cclerk| {
                        starbridge_bounty_board::seed_bounty(exec, "ship the registry", 1_000);
                    },
                    drive: |app, sub| {
                        // A WORKER claims the open bounty — a real verified turn advancing
                        // the bounty state machine (OPEN -> CLAIMED).
                        starbridge_bounty_board::fire_claim(
                            app,
                            &starbridge_bounty_board::WORKER_RIGHTS,
                            "worker",
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    #[cfg(feature = "embedded-executor")]
                    world_drive: |app, world| {
                        use starbridge_bounty_board as b;
                        let app_cell = app.cells()[0].cell();
                        // SEED onto World: program + `seed_bounty` baseline (title hash,
                        // reward, STATE = OPEN).
                        let spine = AppWorldSpine::seed(
                            world,
                            app_cell,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            b::bounty_cell_program(),
                            &[
                                SeedField {
                                    slot: b::TITLE_HASH_SLOT,
                                    value: b::title_hash("ship the registry"),
                                },
                                SeedField {
                                    slot: b::REWARD_SLOT,
                                    value: b::reward_field(1_000),
                                },
                                SeedField {
                                    slot: b::STATE_SLOT,
                                    value: b::state_field(b::STATE_OPEN),
                                },
                            ],
                        );
                        // COMMIT `claim` through World: OPEN -> CLAIMED (StrictMonotonic
                        // re-enforced by World's executor).
                        let receipt = spine.commit(
                            "claim",
                            &b::WORKER_RIGHTS,
                            &b::WORKER_RIGHTS,
                            |_live| b::claim_effects(app_cell, "worker"),
                        )?;
                        Ok((spine, receipt))
                    },
                },
                AppEntry {
                    id: "tussle",
                    name: "Tussle",
                    description:
                        "A two-figure simultaneous-move game — each player commits a sealed move, \
                         both reveal, the frame resolves (a typed set-membership reveal gate).",
                    ctor: starbridge_tussle::tussle_app,
                    seed: |exec, _cclerk| {
                        // Tussle backs its first figure on the executor's own cell.
                        let cell = exec.cell_id();
                        starbridge_tussle::seed_figure(exec, cell);
                    },
                    drive: |app, sub| {
                        // A FIGHTER commits a sealed move on its figure (the executor's
                        // own cell) — a real verified turn writing the sealed-move slot.
                        let figure = sub.cell_id();
                        starbridge_tussle::fire_commit_move(
                            app,
                            figure,
                            &starbridge_tussle::FIGHTER_RIGHTS,
                            &starbridge_tussle::REST_POSE,
                            0x33,
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    #[cfg(feature = "embedded-executor")]
                    world_drive: |app, world| {
                        use starbridge_tussle as t;
                        // Tussle backs its first figure on the agent's OWN cell.
                        let figure = app.cells()[0].cell();
                        // SEED the figure onto World: `figure_deos_program` + the genesis
                        // pose `seed_figure` lays (joints = Relax, POSITION/SCORE = 0,
                        // PHASE = COMMIT, COMMIT_SEAL = 0).
                        let mut seed_fields = Vec::with_capacity(t::N_JOINTS + 4);
                        for j in 0..t::N_JOINTS {
                            seed_fields.push(SeedField {
                                slot: t::slot::JOINT_BASE + j,
                                value: dregg_app_framework::field_from_u64(
                                    t::JointState::Relax.sym(),
                                ),
                            });
                        }
                        seed_fields.push(SeedField {
                            slot: t::slot::POSITION,
                            value: dregg_app_framework::field_from_u64(0),
                        });
                        seed_fields.push(SeedField {
                            slot: t::slot::SCORE,
                            value: dregg_app_framework::field_from_u64(0),
                        });
                        seed_fields.push(SeedField {
                            slot: t::PHASE_SLOT,
                            value: dregg_app_framework::field_from_u64(t::COMMIT),
                        });
                        seed_fields.push(SeedField {
                            slot: t::COMMIT_SEAL_SLOT,
                            value: dregg_app_framework::field_from_u64(0),
                        });
                        let spine = AppWorldSpine::seed(
                            world,
                            figure,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            t::figure_deos_program(),
                            &seed_fields,
                        );
                        // COMMIT `commit_move` through World: write the sealed-move slot
                        // (the SAME seal `fire_commit_move` computes for the rest pose).
                        let figure_id = figure.as_bytes()[0];
                        let seal = t::MoveCommit::new(figure_id, t::REST_POSE, 0x33).seal();
                        let receipt = spine.commit(
                            "commit_move",
                            &t::FIGHTER_RIGHTS,
                            &t::FIGHTER_RIGHTS,
                            |_live| {
                                vec![
                                    dregg_app_framework::Effect::SetField {
                                        cell: figure,
                                        index: t::COMMIT_SEAL_SLOT,
                                        value: seal,
                                    },
                                    dregg_app_framework::Effect::EmitEvent {
                                        cell: figure,
                                        event: dregg_app_framework::Event::new(
                                            dregg_app_framework::symbol("move-committed"),
                                            vec![seal],
                                        ),
                                    },
                                ]
                            },
                        )?;
                        Ok((spine, receipt))
                    },
                },
            ],
        }
    }

    /// The wired apps, in display order.
    pub fn entries(&self) -> &[AppEntry] {
        &self.entries
    }

    /// Look up an entry by its id.
    pub fn get(&self, id: &str) -> Option<&AppEntry> {
        self.entries.iter().find(|e| e.id == id)
    }

    /// **Launch the app with id `id`** in `federation` — the cockpit's launcher
    /// entry point. `None` if no entry has that id.
    pub fn launch(&self, id: &str, federation: [u8; 32]) -> Option<LaunchedRegistryApp> {
        self.get(id).map(|e| e.launch(federation))
    }

    /// **Launch the app with id `id` ONTO the cockpit's LIVE [`World`]** — the
    /// shared-ledger launcher. `None` if no entry has that id; otherwise the
    /// [`AppEntry::launch_on_world`] result (the app's cell + first receipt land on
    /// `world`'s ledger, visible to the cockpit's cell inspector).
    #[cfg(feature = "embedded-executor")]
    pub fn launch_on_world(
        &self,
        id: &str,
        federation: [u8; 32],
        world: Rc<RefCell<World>>,
    ) -> Option<Result<LaunchedOnWorld, WorldFireError>> {
        self.get(id).map(|e| e.launch_on_world(federation, world))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The registry lists the starter set, each with a real ctor + description.
    #[test]
    fn the_standard_registry_lists_the_starter_apps() {
        let reg = AppRegistry::standard();
        let ids: Vec<&str> = reg.entries().iter().map(|e| e.id).collect();
        assert!(ids.contains(&"gallery"));
        assert!(ids.contains(&"sealed-auction"));
        assert!(ids.contains(&"bounty-board"));
        assert!(ids.contains(&"tussle"));
        // Each entry names itself + what it does (the launcher list content).
        for e in reg.entries() {
            assert!(!e.name.is_empty());
            assert!(!e.description.is_empty());
        }
    }

    /// **THE LAUNCH + REAL-TURN PROOF** — launch a registry app into a live
    /// substrate, drive one of its affordances (a real verified turn), and assert
    /// the executor's own [`TurnReceipt`] landed AND the app's new cell state is
    /// visible to a SECOND reader of the SAME ledger (the inspector seam). DONE =
    /// this RAN, not merely compiled.
    #[test]
    fn launching_gallery_fires_a_real_verified_turn_visible_to_a_second_reader() {
        let reg = AppRegistry::standard();
        let federation = [0xA6u8; 32];

        let launched = reg
            .launch("gallery", federation)
            .expect("gallery is in the standard registry");
        let cell = launched.primary_cell();

        // The pre-fire state (a SECOND reader of the live substrate ledger).
        let before = launched
            .substrate
            .cell_state(cell)
            .expect("the seeded gallery cell is live on the substrate ledger");

        // DRIVE one affordance — a REAL verified turn through the embedded executor.
        let receipt = launched
            .drive()
            .expect("the representative affordance fires a real verified turn");

        // A real receipt landed: it carries the executor's own commitment.
        assert_eq!(
            receipt.agent, cell,
            "the verified turn was authored by the app's backing cell"
        );
        assert!(
            receipt.action_count >= 1,
            "the turn carried at least one action"
        );

        // THE SHARED LEDGER: a SECOND reader of the SAME executor sees the new state
        // the fire wrote (the submission slot the gallery `submit` writes). This is
        // the inspector seam — the writer was the verified turn, the reader is the
        // inspector, and they share the substrate ledger.
        let after = launched
            .substrate
            .cell_state(cell)
            .expect("the gallery cell is still live after the fire");
        assert_ne!(
            before.fields, after.fields,
            "the verified turn ADVANCED the cell state the second reader sees \
             (the submission landed on the shared substrate ledger)"
        );
    }

    /// Every wired app launches, seeds, and fires a real verified turn whose state
    /// change is visible to a second reader — the whole starter set is integrated,
    /// not just gallery.
    #[test]
    fn every_wired_app_launches_and_fires_a_real_turn() {
        let reg = AppRegistry::standard();
        let federation = [0x5Eu8; 32];
        for entry in reg.entries() {
            let launched = entry.launch(federation);
            let cell = launched.primary_cell();
            let before = launched
                .substrate
                .cell_state(cell)
                .unwrap_or_else(|| panic!("{} seeds a live backing cell", entry.id));
            let receipt = launched
                .drive()
                .unwrap_or_else(|e| panic!("{} drive fires a real turn: {e:?}", entry.id));
            assert!(
                receipt.action_count >= 1,
                "{} fired a turn with at least one action",
                entry.id
            );
            let after = launched
                .substrate
                .cell_state(cell)
                .unwrap_or_else(|| panic!("{} cell still live after fire", entry.id));
            assert_ne!(
                before.fields, after.fields,
                "{} advanced its cell state on the shared substrate ledger",
                entry.id
            );
        }
    }

    /// **THE SHARED-LEDGER PROOF (the cockpit World, not the side-ledger)** — launch
    /// gallery ONTO a cockpit `World`, and assert the resulting `TurnReceipt` AND the
    /// app's new cell are visible via `World::receipts()` / `World::ledger()` — the
    /// REAL cockpit inspector path. DONE = this RAN.
    #[cfg(feature = "embedded-executor")]
    #[test]
    fn launching_gallery_on_world_commits_its_turn_to_the_cockpit_world_ledger() {
        let world = Rc::new(RefCell::new(World::new()));
        let receipts_before = world.borrow().receipts().len();
        let cells_before = world.borrow().cell_count();

        let reg = AppRegistry::standard();
        let launched = reg
            .launch_on_world("gallery", [0xA6u8; 32], Rc::clone(&world))
            .expect("gallery is in the standard registry")
            .expect("gallery seeds + commits onto the live World");

        let app_cell = launched.primary_cell();

        // THE COCKPIT INSPECTOR PATH (World::ledger): the gallery cell is on the live
        // World ledger, with the submission slot written by the committed turn.
        let cell_on_world = world
            .borrow()
            .ledger()
            .get(&app_cell)
            .cloned()
            .expect("the gallery cell is on the cockpit World ledger (genesis-installed)");
        assert_eq!(
            world.borrow().cell_count(),
            cells_before + 1,
            "the app cell was added to the cockpit World"
        );

        // The committed receipt is authored by the app cell + carried an action.
        assert_eq!(
            launched.receipt.agent, app_cell,
            "the World-committed turn is authored by the gallery cell"
        );
        assert!(launched.receipt.action_count >= 1);

        // THE COCKPIT INSPECTOR PATH (World::receipts): the receipt is in World's OWN
        // provenance log — NOT a framework side-ledger.
        let receipts_after = world.borrow().receipts().len();
        assert_eq!(
            receipts_after,
            receipts_before + 1,
            "the fire landed ONE receipt in World::receipts() (the cockpit inspector log)"
        );
        assert_eq!(
            world.borrow().receipts().last().unwrap().agent,
            app_cell,
            "the World receipt log's last entry is the gallery turn"
        );

        // The submission slot was written on the World cell (slot 4 = SUBMIT_BASE).
        let submit0 = starbridge_gallery::submit_slot(0);
        assert_ne!(
            cell_on_world.state.fields[submit0], [0u8; 32],
            "the submission landed on the cockpit World cell (slot {submit0} written)"
        );
    }

    /// EVERY wired app launches onto the cockpit `World` and lands its cell + first
    /// receipt on `World::ledger()` / `World::receipts()` — the whole starter set is
    /// on the shared cockpit ledger, not just gallery.
    #[cfg(feature = "embedded-executor")]
    #[test]
    fn every_wired_app_launches_on_the_cockpit_world() {
        let reg = AppRegistry::standard();
        for entry in reg.entries() {
            // A fresh World per app (each app backs its primary cell on its own derived
            // id; one World holding two apps would still be fine, but a fresh world
            // isolates the per-app assertion).
            let world = Rc::new(RefCell::new(World::new()));
            let receipts_before = world.borrow().receipts().len();

            let launched = entry
                .launch_on_world([0x5Eu8; 32], Rc::clone(&world))
                .unwrap_or_else(|e| panic!("{} launches on World: {e}", entry.id));
            let app_cell = launched.primary_cell();

            assert!(
                world.borrow().ledger().get(&app_cell).is_some(),
                "{} cell is on the cockpit World ledger",
                entry.id
            );
            assert_eq!(
                world.borrow().receipts().len(),
                receipts_before + 1,
                "{} landed a receipt in World::receipts() (the inspector log)",
                entry.id
            );
            assert_eq!(
                launched.receipt.agent, app_cell,
                "{} World receipt is authored by the app cell",
                entry.id
            );
            assert!(launched.receipt.action_count >= 1, "{} fired an action", entry.id);
        }
    }
}
