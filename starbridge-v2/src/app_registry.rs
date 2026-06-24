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

/// Read a [`dregg_app_framework::FieldElement`] (a 32-byte big-endian field) as the
/// `u64` in its last 8 bytes — the comparison the apps' slot caveats use, so a
/// `world_drive` closure can read the live cursor/meter/counter off `World`'s ledger
/// and advance it (mirrors each app crate's own private `field_tail_u64`/`field_to_u64`).
#[cfg(feature = "embedded-executor")]
fn field_tail_u64(fe: &dregg_app_framework::FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[24..32]);
    u64::from_be_bytes(b)
}

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

/// The per-app **program World drive** closure — the PROGRAM-entry analogue of
/// [`WorldDriveFn`] for apps that are NOT [`DeosApp`]s. `starbridge-polis` ships
/// per-charter content-addressed [`CellProgram`]s directly (not a composed app), so
/// its World drive needs no [`DeosApp`]: it installs a governance cell carrying a
/// polis program onto `World` via [`AppWorldSpine::seed`] and fires one
/// representative governance affordance through [`AppWorldSpine::commit`]. Receives
/// only the shared `World`; returns the seeded spine + the committed receipt — the
/// SAME contract [`WorldDriveFn`] honours, minus the framework app.
#[cfg(feature = "embedded-executor")]
type ProgramWorldDriveFn =
    fn(Rc<RefCell<World>>) -> Result<(AppWorldSpine, TurnReceipt), WorldFireError>;

/// The framework backend of an [`AppEntry`] — a pre-built [`DeosApp`] over the app
/// framework's [`AppSubstrate`]. Carries the REAL ctor + seed + drive (the
/// framework-substrate path) and the `world_drive` (the cockpit-`World` path).
#[derive(Clone, Copy)]
struct FrameworkBackend {
    /// The real `*_app(cipherclerk, executor) -> DeosApp` ctor.
    ctor: CtorFn,
    /// Seed the backing cell's program + genesis state on the substrate.
    seed: SeedFn,
    /// Fire one representative affordance (a real verified turn) — the proof.
    drive: DriveFn,
    /// Seed the app's cell onto the cockpit's LIVE [`World`] and commit one
    /// representative affordance THROUGH it.
    #[cfg(feature = "embedded-executor")]
    world_drive: WorldDriveFn,
}

/// How an [`AppEntry`] is realized — either a framework [`DeosApp`]
/// ([`AppBackend::Framework`], the 18 starbridge-apps) or a polis-style PROGRAM
/// ([`AppBackend::Program`], which installs a bare [`CellProgram`] onto `World` and
/// fires one affordance, with NO [`DeosApp`]). One registry, two backends — the
/// program backend is the minimal clean variant for apps that yield a `CellProgram`
/// directly rather than a composed app.
#[derive(Clone, Copy)]
enum AppBackend {
    /// A pre-built [`DeosApp`] over the app framework (the 18 starbridge-apps).
    Framework(FrameworkBackend),
    /// A program-only app (polis): installs a [`CellProgram`] onto `World` + fires
    /// one affordance, no [`DeosApp`]. It has NO framework-substrate path (it cannot
    /// build a `DeosApp`), so [`AppEntry::launch`] returns `None` for it — only the
    /// cockpit-`World` path ([`AppEntry::launch_on_world`]) applies. Gated on
    /// `embedded-executor` (the program drive carries `World` types); the
    /// framework-only registry build never constructs a `Program` entry.
    #[cfg(feature = "embedded-executor")]
    Program(ProgramWorldDriveFn),
    /// On a framework-only registry build (`app-registry` without
    /// `embedded-executor`), there is no `World` type, so a program entry cannot
    /// exist — this variant is uninhabited there. (Polis is only wired in the
    /// `embedded-executor` build, which the cockpit always has.)
    #[cfg(not(feature = "embedded-executor"))]
    Program(std::convert::Infallible),
}

/// **One entry in the app registry** — a pre-built starbridge-app the cockpit can
/// launch. Names the app (id / display name / one-line description) and carries the
/// REAL backend (framework ctor+seed+drive, or a polis-style program drive) so a
/// launch is wiring, not re-implementation.
#[derive(Clone, Copy)]
pub struct AppEntry {
    /// A stable, short id (the launch key / palette token), e.g. `"gallery"`.
    pub id: &'static str,
    /// The display name shown in the launcher list.
    pub name: &'static str,
    /// A one-line description of what the app does (what the user reads before
    /// launching).
    pub description: &'static str,
    /// How this entry is realized (framework `DeosApp` or polis-style program).
    backend: AppBackend,
}

impl AppEntry {
    /// Construct a **framework** entry (a pre-built [`DeosApp`]). The 18
    /// starbridge-apps use this.
    #[cfg(feature = "embedded-executor")]
    const fn framework(
        id: &'static str,
        name: &'static str,
        description: &'static str,
        ctor: CtorFn,
        seed: SeedFn,
        drive: DriveFn,
        world_drive: WorldDriveFn,
    ) -> Self {
        AppEntry {
            id,
            name,
            description,
            backend: AppBackend::Framework(FrameworkBackend {
                ctor,
                seed,
                drive,
                world_drive,
            }),
        }
    }

    /// Construct a **program** entry (polis): a [`CellProgram`] installed onto
    /// `World` + one representative affordance, with NO [`DeosApp`]. Only the
    /// cockpit-`World` path ([`AppEntry::launch_on_world`]) applies.
    #[cfg(feature = "embedded-executor")]
    const fn program(
        id: &'static str,
        name: &'static str,
        description: &'static str,
        program_world_drive: ProgramWorldDriveFn,
    ) -> Self {
        AppEntry {
            id,
            name,
            description,
            backend: AppBackend::Program(program_world_drive),
        }
    }

    /// **Launch this app over the app-framework substrate** — build a fresh live
    /// [`AppSubstrate`] in `federation`, instantiate the [`DeosApp`] over it, seed the
    /// backing cell so its program bites, and return the [`LaunchedRegistryApp`]. The
    /// app's affordances now fire REAL verified turns on the substrate ledger (drive
    /// them with [`LaunchedRegistryApp::drive`]); its cell + state are visible to a
    /// second reader of the substrate.
    ///
    /// `None` for a PROGRAM entry (polis) — it has no [`DeosApp`]/framework-substrate
    /// path; launch it onto the cockpit `World` with [`AppEntry::launch_on_world`].
    pub fn launch(&self, federation: [u8; 32]) -> Option<LaunchedRegistryApp> {
        let fw = match &self.backend {
            AppBackend::Framework(fw) => fw,
            #[cfg(feature = "embedded-executor")]
            AppBackend::Program(_) => return None,
            #[cfg(not(feature = "embedded-executor"))]
            AppBackend::Program(never) => match *never {},
        };
        let substrate = AppSubstrate::new(federation);
        let app = (fw.ctor)(substrate.cipherclerk(), substrate.executor());
        (fw.seed)(substrate.executor(), substrate.cipherclerk());
        Some(LaunchedRegistryApp {
            id: self.id,
            app,
            substrate,
            drive: fw.drive,
        })
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
        match &self.backend {
            AppBackend::Framework(fw) => {
                let substrate = AppSubstrate::new(federation);
                let app = (fw.ctor)(substrate.cipherclerk(), substrate.executor());
                let (spine, receipt) = (fw.world_drive)(&app, world)?;
                Ok(LaunchedOnWorld {
                    id: self.id,
                    app: Some(app),
                    spine,
                    receipt,
                })
            }
            // A PROGRAM entry (polis) needs no `DeosApp`/`AppSubstrate` — it installs a
            // bare `CellProgram` onto `World` and fires one affordance directly.
            AppBackend::Program(program_world_drive) => {
                let (spine, receipt) = (program_world_drive)(world)?;
                Ok(LaunchedOnWorld {
                    id: self.id,
                    app: None,
                    spine,
                    receipt,
                })
            }
        }
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
    /// The composed deos app (cells × affordances) — `None` for a PROGRAM entry
    /// (polis), which has no [`DeosApp`]: its cell + program live directly on `World`
    /// via the [`Self::spine`].
    pub app: Option<DeosApp>,
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
                AppEntry::framework(
                    "gallery",
                    "Sealed Gallery",

                        "A juried art gallery with sealed (commit-reveal) submissions — \
                         artists commit, the curator closes, artists reveal, the curator features.",
                    starbridge_gallery::gallery_app,
                    |exec, _cclerk| {
                        starbridge_gallery::seed_gallery(exec, "curator");
                    },
                    |app, sub| {
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
                    |app, world| {
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
                    }
                ),
                AppEntry::framework(
                    "sealed-auction",
                    "Sealed Auction",

                        "A sealed-bid (commit-reveal) auction — bidders commit hashed bids, \
                         the seller closes commits, bidders reveal, the seller resolves the winner.",
                    starbridge_sealed_auction::auction_app,
                    |exec, _cclerk| {
                        starbridge_sealed_auction::seed_auction(exec, "seller");
                    },
                    |app, sub| {
                        // A BIDDER commits a sealed bid in the COMMIT phase.
                        starbridge_sealed_auction::fire_commit_bid(
                            app,
                            &starbridge_sealed_auction::BIDDER_RIGHTS,
                            dregg_app_framework::field_from_u64(0xB1D),
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
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
                    }
                ),
                AppEntry::framework(
                    "bounty-board",
                    "Bounty Board",

                        "A bounty with an escrowed reward — a worker claims it, submits work, \
                         and the poster pays out (each step a cap-gated state-machine turn).",
                    starbridge_bounty_board::bounty_app,
                    |exec, _cclerk| {
                        starbridge_bounty_board::seed_bounty(exec, "ship the registry", 1_000);
                    },
                    |app, sub| {
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
                    |app, world| {
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
                    }
                ),
                AppEntry::framework(
                    "tussle",
                    "Tussle",

                        "A two-figure simultaneous-move game — each player commits a sealed move, \
                         both reveal, the frame resolves (a typed set-membership reveal gate).",
                    starbridge_tussle::tussle_app,
                    |exec, _cclerk| {
                        // Tussle backs its first figure on the executor's own cell.
                        let cell = exec.cell_id();
                        starbridge_tussle::seed_figure(exec, cell);
                    },
                    |app, sub| {
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
                    |app, world| {
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
                    }
                ),
                // ───────────────────────────────────────────────────────────
                // THE SECOND WAVE — the framework-using starbridge-apps wired
                // onto the cockpit's LIVE `World` ledger. Each re-expresses ONE
                // representative affordance through `AppWorldSpine::commit`
                // (`World::turn` → `World::commit_turn`), reusing the app crate's
                // OWN `*_program()` + `*_effects()`/effect recipe so the World
                // path fires the SAME verified turn the framework path does —
                // only the ledger is the cockpit's.
                //
                // THE SENDER-BOUND TIER (`commit_as`) — supply-chain /
                // identity / governed-namespace, whose representative affordance
                // reads the turn's SENDER (`SenderInSlot` / `SenderAuthorized`),
                // are NOW wired too. The executor derives `ctx.sender` from the
                // AGENT cell's pubkey (not the `Unchecked` authorization), and the
                // agent IS the app cell (seeded as `Cell::with_balance(pubkey, …)`),
                // so seeding the sender slot/root over THAT pubkey + attaching the
                // single-member membership proof clears the sender clause. (polis
                // and first-room are not `DeosApp`s. See the module note.)
                // ───────────────────────────────────────────────────────────
                AppEntry::framework(
                    "agent-orchestration",
                    "Agent Orchestration",

                        "A coordinator board with a shared per-worker spend budget — a worker fires one \
                         metered step, advancing the no-replay epoch (the Σspend ≤ budget gate bites).",
                    starbridge_agent_orchestration::deos::orchestration_app,
                    |exec, _cclerk| {
                        use starbridge_agent_orchestration as o;
                        o::seed_board(exec, o::DEFAULT_CREATION_BUDGET, "coordinator");
                    },
                    |app, sub| {
                        use starbridge_agent_orchestration as o;
                        // A WORKER fires one metered step (worker A, cost 1).
                        let board = &app.cells()[0];
                        o::deos::fire_worker_step(
                            board,
                            &o::deos::WORKER_RIGHTS,
                            o::WorkerSlot::A,
                            1,
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
                        use starbridge_agent_orchestration as o;
                        let board = app.cells()[0].cell();
                        // SEED the board onto World: `coordinator_program` (the
                        // Σspend ≤ budget / Monotonic meters / StrictMonotonic epoch
                        // policy) + the `seed_board` baseline (lead, budget, spends=0,
                        // EPOCH=1 ⇒ board OPEN).
                        let spine = AppWorldSpine::seed(
                            world,
                            board,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            o::coordinator_program(),
                            &[
                                SeedField {
                                    slot: o::LEAD_SLOT as usize,
                                    value: dregg_app_framework::field_from_bytes(b"coordinator"),
                                },
                                SeedField {
                                    slot: o::BUDGET_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(
                                        o::DEFAULT_CREATION_BUDGET,
                                    ),
                                },
                                SeedField {
                                    slot: o::SPENT_A_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: o::SPENT_B_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: o::EPOCH_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(1),
                                },
                            ],
                        );
                        // COMMIT `worker_step` through World: read the live spend +
                        // epoch off World's ledger (so the meter accumulates), then
                        // SPENT_A += cost, EPOCH += 1 (the SAME effects `fire_worker_step`
                        // computes).
                        let receipt = spine.commit(
                            "worker_step",
                            &o::deos::WORKER_RIGHTS,
                            &o::deos::WORKER_RIGHTS,
                            |live| {
                                let spend_slot = o::WorkerSlot::A.spend_slot() as usize;
                                let live_spent = field_tail_u64(&live.fields[spend_slot]);
                                let live_epoch = field_tail_u64(&live.fields[o::EPOCH_SLOT as usize]);
                                vec![
                                    dregg_app_framework::Effect::SetField {
                                        cell: board,
                                        index: spend_slot,
                                        value: dregg_app_framework::field_from_u64(
                                            live_spent.saturating_add(1),
                                        ),
                                    },
                                    dregg_app_framework::Effect::SetField {
                                        cell: board,
                                        index: o::EPOCH_SLOT as usize,
                                        value: dregg_app_framework::field_from_u64(
                                            live_epoch.saturating_add(1),
                                        ),
                                    },
                                ]
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "agent-provenance",
                    "Agent Provenance",

                        "A hash-linked provenance log — a recorder appends one entry that chains to the \
                         prior tip (the link-hash chain the executor's WriteOnce board re-enforces).",
                    starbridge_agent_provenance::provenance_app,
                    |exec, _cclerk| {
                        starbridge_agent_provenance::seed_log(exec, b"genesis");
                    },
                    |app, sub| {
                        use starbridge_agent_provenance as p;
                        // A RECORDER appends one claim to the log.
                        p::fire_append_entry(
                            app,
                            &p::RECORDER_RIGHTS,
                            sub.cipherclerk(),
                            sub.executor(),
                            &dregg_app_framework::field_from_u64(0xC1A1),
                        )
                    },
                    |app, world| {
                        use starbridge_agent_provenance as p;
                        let log = app.cells()[0].cell();
                        // SEED the log onto World: `provenance_cell_program` + the
                        // `seed_log` genesis chain (entry[0] = link(0, "genesis"),
                        // HEAD=1, TIP=that digest).
                        let genesis_claim = p::claim_digest(b"genesis");
                        let genesis_link = p::link_hash(&p::GENESIS_PREV, &genesis_claim);
                        let spine = AppWorldSpine::seed(
                            world,
                            log,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            p::provenance_cell_program(),
                            &[
                                SeedField {
                                    slot: p::entry_slot(0),
                                    value: genesis_link,
                                },
                                SeedField {
                                    slot: p::HEAD_SLOT,
                                    value: dregg_app_framework::field_from_u64(1),
                                },
                                SeedField {
                                    slot: p::TIP_SLOT,
                                    value: genesis_link,
                                },
                            ],
                        );
                        // COMMIT `append_entry` through World: `append_effects` reads
                        // the live HEAD/TIP off World's ledger and chains the next entry.
                        let claim = dregg_app_framework::field_from_u64(0xC1A1);
                        let receipt = spine.commit(
                            "append_entry",
                            &p::RECORDER_RIGHTS,
                            &p::RECORDER_RIGHTS,
                            |live| p::append_effects(log, live, &claim),
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "compartment-workflow-mandate",
                    "Compartment Workflow Mandate",

                        "A clearance-gated workflow charter (review → redact → sign) — an officer advances \
                         one step, presenting a clearance that must dominate the entered step's compartment.",
                    starbridge_compartment_workflow_mandate::workflow_app,
                    |exec, _cclerk| {
                        use starbridge_compartment_workflow_mandate as c;
                        c::seed_workflow(
                            exec,
                            c::DEFAULT_COMMITMENT_ANCHOR,
                            c::DEFAULT_CHARTER_STEPS,
                            c::charter_clearance_root(),
                            c::DEFAULT_STEP_SPEND_POLICY,
                        );
                    },
                    |app, sub| {
                        use starbridge_compartment_workflow_mandate as c;
                        // An OFFICER advances the first step (review), presenting the
                        // officer clearance (which dominates every charter compartment).
                        c::fire_advance_step(
                            app,
                            &c::OPERATOR_RIGHTS,
                            c::officer_label(),
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
                        use starbridge_compartment_workflow_mandate as c;
                        let cell = app.cells()[0].cell();
                        // SEED onto World: `cwm_cell_program` (the Cases program — the
                        // `advance_step` case binds ClearanceDominates) + the `seed_workflow`
                        // baseline (anchor, charter terminal, clearance graph root, spend
                        // policy, STEP_CURSOR=0).
                        let spine = AppWorldSpine::seed(
                            world,
                            cell,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            c::cwm_cell_program(),
                            &[
                                SeedField {
                                    slot: c::COMMITMENT_ANCHOR_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(
                                        c::DEFAULT_COMMITMENT_ANCHOR,
                                    ),
                                },
                                SeedField {
                                    slot: c::CHARTER_TERMINAL_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(
                                        c::DEFAULT_CHARTER_STEPS,
                                    ),
                                },
                                SeedField {
                                    slot: c::CLEARANCE_GRAPH_ROOT_SLOT as usize,
                                    value: c::charter_clearance_root(),
                                },
                                SeedField {
                                    slot: c::SPEND_POLICY_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(
                                        c::DEFAULT_STEP_SPEND_POLICY,
                                    ),
                                },
                                SeedField {
                                    slot: c::STEP_CURSOR_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                            ],
                        );
                        // COMMIT `advance_step` through World: advance cursor 0 → 1
                        // (entering step 0 = review), presenting the officer clearance
                        // and the review compartment label — exactly what `fire_advance_step`
                        // materializes for the executor's ClearanceDominates tooth.
                        let review_compartment =
                            c::WorkflowPhase::CHARTER[0].compartment_label();
                        let receipt = spine.commit(
                            "advance_step",
                            &c::OPERATOR_RIGHTS,
                            &c::OPERATOR_RIGHTS,
                            |_live| {
                                c::advance_effects(cell, 1, c::officer_label(), review_compartment)
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "compute-exchange",
                    "Compute Exchange",

                        "A compute-job market (post → bid → settle) — a provider bids on the posted job, \
                         advancing the job state machine (the settle conservation AffineEq waits downstream).",
                    starbridge_compute_exchange::job_app,
                    |exec, _cclerk| {
                        starbridge_compute_exchange::seed_job(exec, "requester-corp", 1_000);
                    },
                    |app, sub| {
                        use starbridge_compute_exchange as j;
                        // A PROVIDER bids on the posted job.
                        j::fire_bid(
                            app,
                            &j::PROVIDER_RIGHTS,
                            "provider-gpu",
                            750,
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
                        use starbridge_compute_exchange as j;
                        let job = app.cells()[0].cell();
                        // SEED onto World: `job_program` (Cases: post/bid/settle) + the
                        // `seed_job` baseline (requester hash, budget, spec, BID=0,
                        // STATE = POSTED).
                        let spine = AppWorldSpine::seed(
                            world,
                            job,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            j::job_program(),
                            &[
                                SeedField {
                                    slot: j::REQUESTER_HASH_SLOT,
                                    value: dregg_app_framework::field_from_bytes(b"requester-corp"),
                                },
                                SeedField {
                                    slot: j::BUDGET_SLOT,
                                    value: dregg_app_framework::field_from_u64(1_000),
                                },
                                SeedField {
                                    slot: j::SPEC_HASH_SLOT,
                                    value: j::spec_digest(b"render-frame-batch"),
                                },
                                SeedField {
                                    slot: j::BID_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: j::STATE_SLOT,
                                    value: dregg_app_framework::field_from_u64(j::STATE_POSTED),
                                },
                            ],
                        );
                        // COMMIT `bid` through World: POSTED → BID, recording the provider
                        // + price (the SAME `bid_effects` the framework path fires).
                        let receipt = spine.commit(
                            "bid",
                            &j::PROVIDER_RIGHTS,
                            &j::PROVIDER_RIGHTS,
                            |_live| j::bid_effects(job, "provider-gpu", 750),
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "escrow-market",
                    "Escrow Market",

                        "A two-party escrow marketplace (list → fund → ship → settle) — a buyer funds the \
                         listed item into escrow (the settle release+refund=escrowed conservation waits downstream).",
                    starbridge_escrow_market::escrow_app,
                    |exec, _cclerk| {
                        starbridge_escrow_market::seed_escrow(exec, "acme-corp", 1_000);
                    },
                    |app, sub| {
                        use starbridge_escrow_market as e;
                        // A BUYER funds the listed item.
                        e::fire_fund(
                            app,
                            &e::BUYER_RIGHTS,
                            "buyer-bob",
                            500,
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
                        use starbridge_escrow_market as e;
                        let escrow = app.cells()[0].cell();
                        // SEED onto World: `escrow_program` (Cases: list/fund/ship/settle)
                        // + the `seed_escrow` baseline (seller hash, ceiling, escrowed=0,
                        // STATE = LISTED).
                        let spine = AppWorldSpine::seed(
                            world,
                            escrow,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            e::escrow_program(),
                            &[
                                SeedField {
                                    slot: e::SELLER_HASH_SLOT,
                                    value: dregg_app_framework::field_from_bytes(b"acme-corp"),
                                },
                                SeedField {
                                    slot: e::CEILING_SLOT,
                                    value: dregg_app_framework::field_from_u64(1_000),
                                },
                                SeedField {
                                    slot: e::ESCROWED_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: e::STATE_SLOT,
                                    value: dregg_app_framework::field_from_u64(e::STATE_LISTED),
                                },
                            ],
                        );
                        // COMMIT `fund` through World: LISTED → FUNDED, escrowing the
                        // buyer's amount (the SAME `fund_effects` the framework path fires).
                        let receipt = spine.commit(
                            "fund",
                            &e::BUYER_RIGHTS,
                            &e::BUYER_RIGHTS,
                            |_live| e::fund_effects(escrow, "buyer-bob", 500),
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "nameservice",
                    "Name Service",

                        "A registered-name record (owner / expiry / revocation) — the owner renews the name, \
                         advancing the expiry (the executor re-enforces Monotonic(EXPIRY) + WriteOnce(NAME)).",
                    starbridge_nameservice::name_app,
                    |exec, cclerk| {
                        use starbridge_nameservice as n;
                        n::seed_name(
                            exec,
                            "deos.dregg",
                            cclerk.public_key().0,
                            n::DEFAULT_RENT_EPOCH_BLOCKS,
                        );
                    },
                    |app, sub| {
                        use starbridge_nameservice as n;
                        // The OWNER renews the name (advances EXPIRY by one rent epoch).
                        n::fire_renew(app, &n::OWNER_RIGHTS, sub.cipherclerk(), sub.executor())
                    },
                    |app, world| {
                        use starbridge_nameservice as n;
                        let name_cell = app.cells()[0].cell();
                        let owner = app.cipherclerk().public_key().0;
                        // SEED onto World: `name_cell_program` (WriteOnce NAME + Monotonic
                        // EXPIRY + WriteOnce REVOKED) + the `seed_name` baseline.
                        let spine = AppWorldSpine::seed(
                            world,
                            name_cell,
                            owner,
                            default_domain_token(),
                            n::name_cell_program(),
                            &[
                                SeedField {
                                    slot: n::NAME_HASH_SLOT,
                                    value: dregg_app_framework::field_from_bytes(b"deos.dregg"),
                                },
                                SeedField {
                                    slot: n::OWNER_HASH_SLOT,
                                    value: dregg_app_framework::field_from_bytes(&owner),
                                },
                                SeedField {
                                    slot: n::EXPIRY_SLOT,
                                    value: dregg_app_framework::field_from_u64(
                                        n::DEFAULT_RENT_EPOCH_BLOCKS,
                                    ),
                                },
                                SeedField {
                                    slot: n::REVOKED_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                            ],
                        );
                        // COMMIT `renew` through World: EXPIRY += one rent epoch, read off
                        // World's live state (Monotonic(EXPIRY) holds) — the SAME advance
                        // `fire_renew` computes.
                        let receipt = spine.commit(
                            "renew",
                            &n::OWNER_RIGHTS,
                            &n::OWNER_RIGHTS,
                            |live| {
                                let live_expiry = field_tail_u64(&live.fields[n::EXPIRY_SLOT]);
                                let new_expiry =
                                    live_expiry.saturating_add(n::DEFAULT_RENT_EPOCH_BLOCKS);
                                vec![dregg_app_framework::Effect::SetField {
                                    cell: name_cell,
                                    index: n::EXPIRY_SLOT,
                                    value: dregg_app_framework::field_from_u64(new_expiry),
                                }]
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "privacy-voting",
                    "Privacy Voting",

                        "A public-tally poll — an administrator records one vote onto the poll's running tally \
                         (the executor re-enforces the poll invariants; the poll stays open until closed).",
                    starbridge_privacy_voting::voting_app,
                    |exec, _cclerk| {
                        starbridge_privacy_voting::seed_poll(exec, "ship it?");
                    },
                    |app, sub| {
                        use starbridge_privacy_voting as v;
                        // An ADMINISTRATOR records a YES vote onto the poll tally.
                        v::fire_record_tally(
                            app,
                            &v::ADMINISTRATOR_RIGHTS,
                            v::VOTE_YES,
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
                        use starbridge_privacy_voting as v;
                        // The poll cell is the agent's own cell (cells()[0]).
                        let poll = app.cells()[0].cell();
                        // SEED the poll onto World: `poll_cell_program` + the `seed_poll`
                        // baseline (question hash, tallies = 0, CLOSED = 0).
                        let spine = AppWorldSpine::seed(
                            world,
                            poll,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            v::poll_cell_program(),
                            &[
                                SeedField {
                                    slot: v::QUESTION_HASH_SLOT,
                                    value: v::question_hash("ship it?"),
                                },
                                SeedField {
                                    slot: v::TALLY_YES_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: v::TALLY_NO_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: v::TALLY_ABSTAIN_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: v::CLOSED_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                            ],
                        );
                        // COMMIT `record_tally` through World: increment the YES tally,
                        // read off World's live state (the SAME accumulating fire
                        // `fire_record_tally` performs).
                        let tally_slot = v::tally_slot_for_choice(v::VOTE_YES);
                        let receipt = spine.commit(
                            "record_tally",
                            &v::ADMINISTRATOR_RIGHTS,
                            &v::ADMINISTRATOR_RIGHTS,
                            |live| {
                                let live_tally = field_tail_u64(&live.fields[tally_slot]);
                                vec![dregg_app_framework::Effect::SetField {
                                    cell: poll,
                                    index: tally_slot,
                                    value: dregg_app_framework::field_from_u64(
                                        live_tally.saturating_add(1),
                                    ),
                                }]
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "storage-gateway-mandate",
                    "Storage Gateway Mandate",

                        "A metered storage gateway (put / get / list under a volume ceiling) — a writer puts \
                         an object, debiting the volume meter (the executor re-enforces volume_spent ≤ ceiling).",
                    starbridge_storage_gateway_mandate::gateway_app,
                    |exec, _cclerk| {
                        use starbridge_storage_gateway_mandate as s;
                        s::seed_gateway(
                            exec,
                            s::DEFAULT_COMMITMENT_ANCHOR,
                            s::DEFAULT_VOLUME_CEILING,
                            s::DEFAULT_KEY_PREFIX,
                            s::DEFAULT_READ_COMPARTMENT,
                        );
                    },
                    |app, sub| {
                        use starbridge_storage_gateway_mandate as s;
                        // A WRITER puts a 1-unit object under the prefix.
                        s::fire_put(
                            app,
                            &s::WRITER_RIGHTS,
                            sub.cipherclerk(),
                            sub.executor(),
                            "uploads/first",
                            1,
                        )
                    },
                    |app, world| {
                        use starbridge_storage_gateway_mandate as s;
                        let gateway = app.cells()[0].cell();
                        // SEED onto World: `gateway_program_with_clearance` (the Cases
                        // program: get binds ClearanceDominates, put/list bind the meter)
                        // + the `seed_gateway` baseline (anchor, ceiling, key prefix, read
                        // compartment, clearance graph root, VOLUME_SPENT=0).
                        let spine = AppWorldSpine::seed(
                            world,
                            gateway,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            s::gateway_program_with_clearance(),
                            &[
                                SeedField {
                                    slot: s::COMMITMENT_ANCHOR_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(
                                        s::DEFAULT_COMMITMENT_ANCHOR,
                                    ),
                                },
                                SeedField {
                                    slot: s::VOLUME_CEILING_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(
                                        s::DEFAULT_VOLUME_CEILING,
                                    ),
                                },
                                SeedField {
                                    slot: s::KEY_PREFIX_HASH_SLOT as usize,
                                    value: s::key_prefix_field(s::DEFAULT_KEY_PREFIX),
                                },
                                SeedField {
                                    slot: s::READ_COMPARTMENT_SLOT as usize,
                                    value: dregg_app_framework::field_from_bytes(
                                        s::DEFAULT_READ_COMPARTMENT.as_bytes(),
                                    ),
                                },
                                SeedField {
                                    slot: s::CLEARANCE_GRAPH_ROOT_SLOT as usize,
                                    value: s::clearance_root(),
                                },
                                SeedField {
                                    slot: s::VOLUME_SPENT_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                            ],
                        );
                        // COMMIT `put` through World: read the live volume meter off
                        // World's ledger, debit the object size, and write the object key
                        // + last-op (the SAME `put_effects` the framework path fires).
                        let key = "uploads/first";
                        let blob_hash = s::object_key_field(key);
                        let receipt = spine.commit(
                            "put",
                            &s::WRITER_RIGHTS,
                            &s::WRITER_RIGHTS,
                            |live| {
                                let live_spent =
                                    field_tail_u64(&live.fields[s::VOLUME_SPENT_SLOT as usize]);
                                let new_spent = live_spent.saturating_add(1);
                                s::put_effects(gateway, key, new_spent, blob_hash)
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "subscription",
                    "Subscription Feed",

                        "A publish/consume message feed under a capacity bound — a publisher publishes one \
                         message, advancing the head cursor + folding the message-commitment root.",
                    starbridge_subscription::subscription_deos_app,
                    |exec, _cclerk| {
                        starbridge_subscription::seed_feed(exec, 16, "owner");
                    },
                    |app, sub| {
                        use starbridge_subscription as s;
                        // A PUBLISHER publishes one message onto the feed.
                        s::fire_publish(
                            app,
                            &s::PUBLISHER_RIGHTS,
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
                        use starbridge_subscription as s;
                        let feed = app.cells()[0].cell();
                        // SEED onto World: `feed_invariants_program` (the FLAT invariants
                        // the deos surface installs — no SenderAuthorized, so the World
                        // single-custody path admits a plain publish) + the `seed_feed`
                        // baseline (capacity, owner hash, SEQ_HEAD=1, SEQ_TAIL=0).
                        let spine = AppWorldSpine::seed(
                            world,
                            feed,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            s::feed_invariants_program(),
                            &[
                                SeedField {
                                    slot: s::CAPACITY_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(16),
                                },
                                SeedField {
                                    slot: s::OWNER_PK_HASH_SLOT as usize,
                                    value: dregg_app_framework::field_from_bytes(b"owner"),
                                },
                                SeedField {
                                    slot: s::SEQ_HEAD_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(1),
                                },
                                SeedField {
                                    slot: s::SEQ_TAIL_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                            ],
                        );
                        // COMMIT `publish` through World: read the live head off World's
                        // ledger, advance it, and fold the new message-commitment root
                        // (the SAME `publish_effects` the framework path fires).
                        let payload = dregg_app_framework::field_from_u64(0xF33D);
                        let receipt = spine.commit(
                            "publish",
                            &s::PUBLISHER_RIGHTS,
                            &s::PUBLISHER_RIGHTS,
                            |live| {
                                let live_head =
                                    field_tail_u64(&live.fields[s::SEQ_HEAD_SLOT as usize]);
                                let new_head = live_head.saturating_add(1);
                                let prev_root = live.fields[s::MESSAGE_ROOT_SLOT as usize];
                                let new_root =
                                    s::fold_message_root(&prev_root, new_head, &payload);
                                s::publish_effects(feed, new_head, new_root, payload)
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "swarm-orchestration",
                    "Swarm Orchestration",

                        "A swarm dispatch board with a per-worker spend budget — the lead dispatches one task \
                         to a worker, debiting its meter + advancing the no-replay epoch (Σspend ≤ budget bites).",
                    starbridge_swarm_orchestration::board_app,
                    |exec, _cclerk| {
                        starbridge_swarm_orchestration::seed_board(exec, "lead", 1_000);
                    },
                    |app, sub| {
                        use starbridge_swarm_orchestration as w;
                        // The LEAD dispatches one task (cost 1) to worker A.
                        let board = app.cells()[0].cell();
                        w::fire_dispatch(
                            app,
                            &w::LEAD_RIGHTS,
                            sub.cipherclerk(),
                            sub.executor(),
                            w::Worker::A,
                            board,
                            1,
                            "task-0",
                        )
                    },
                    |app, world| {
                        use starbridge_swarm_orchestration as w;
                        let board = app.cells()[0].cell();
                        // SEED onto World: `coordinator_program` (AffineLe budget,
                        // WriteOnce BUDGET/LEAD, Monotonic meters, StrictMonotonic EPOCH)
                        // + the `seed_board` baseline (lead, budget, spends=0, EPOCH=1).
                        let spine = AppWorldSpine::seed(
                            world,
                            board,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            w::coordinator_program(),
                            &[
                                SeedField {
                                    slot: w::LEAD_SLOT as usize,
                                    value: dregg_app_framework::field_from_bytes(b"lead"),
                                },
                                SeedField {
                                    slot: w::BUDGET_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(1_000),
                                },
                                SeedField {
                                    slot: w::SPENT_A_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: w::SPENT_B_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: w::EPOCH_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(1),
                                },
                            ],
                        );
                        // COMMIT `dispatch` through World: read the live worker-A meter +
                        // epoch off World's ledger, debit cost 1, advance the epoch (the
                        // SAME `dispatch_effects` the framework path fires).
                        let receipt = spine.commit(
                            "dispatch",
                            &w::LEAD_RIGHTS,
                            &w::LEAD_RIGHTS,
                            |live| {
                                let spend_slot = w::Worker::A.spend_slot() as usize;
                                let live_spent = field_tail_u64(&live.fields[spend_slot]);
                                let live_epoch = field_tail_u64(&live.fields[w::EPOCH_SLOT as usize]);
                                w::dispatch_effects(
                                    board,
                                    w::Worker::A,
                                    board,
                                    live_spent.saturating_add(1),
                                    live_epoch.saturating_add(1),
                                    1,
                                    "task-0",
                                )
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "tool-access-delegation",
                    "Tool Access Delegation",

                        "A rate-limited tool-access mandate — a worker invokes the tool once, ticking the \
                         call counter (the executor re-enforces calls_made ≤ rate_limit + the deadline gate).",
                    starbridge_tool_access_delegation::tad_app,
                    |exec, _cclerk| {
                        starbridge_tool_access_delegation::seed_mandate(exec, "search-mcp", 8, 0);
                    },
                    |app, sub| {
                        use starbridge_tool_access_delegation as t;
                        // A WORKER invokes the tool once.
                        t::fire_invoke(app, &t::WORKER_RIGHTS, sub.cipherclerk(), sub.executor())
                    },
                    |app, world| {
                        use starbridge_tool_access_delegation as t;
                        let mandate = app.cells()[0].cell();
                        // SEED onto World: `tad_cell_program` (Cases: the `invoke_tool`
                        // case binds Monotonic CALLS_MADE + the deadline-height gate) + the
                        // `seed_mandate` baseline (rate limit, tool id, deadline=0, CALLS=0).
                        let spine = AppWorldSpine::seed(
                            world,
                            mandate,
                            app.cipherclerk().public_key().0,
                            default_domain_token(),
                            t::tad_cell_program(),
                            &[
                                SeedField {
                                    slot: t::RATE_LIMIT_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(8),
                                },
                                SeedField {
                                    slot: t::TOOL_ID_SLOT as usize,
                                    value: dregg_app_framework::field_from_bytes(b"search-mcp"),
                                },
                                SeedField {
                                    slot: t::DEADLINE_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: t::CALLS_MADE_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                            ],
                        );
                        // COMMIT through World carrying the `invoke_tool` METHOD SYMBOL
                        // (the Cases dispatch case; the surface name is `invoke` but the
                        // wire method MUST be `invoke_tool` or the Cases program default-
                        // denies). Read the live call counter, tick it (Monotonic holds).
                        let receipt = spine.commit(
                            "invoke_tool",
                            &t::WORKER_RIGHTS,
                            &t::WORKER_RIGHTS,
                            |live| {
                                let live_calls =
                                    field_tail_u64(&live.fields[t::CALLS_MADE_SLOT as usize]);
                                t::invoke_effects(mandate, live_calls.saturating_add(1))
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                // ───────────────────────────────────────────────────────────
                // THE SENDER-BOUND WAVE — affordances that read the turn's
                // SENDER, committed through `AppWorldSpine::commit_as`.
                // ───────────────────────────────────────────────────────────
                AppEntry::framework(
                    "supply-chain-provenance",
                    "Supply-Chain Provenance",

                        "A custody-chain item (mint → handoff) — the incoming custodian accepts custody, \
                         advancing the actor-bound baton (the SenderInSlot(CUSTODIAN) tooth bites).",
                    starbridge_supply_chain_provenance::item_app,
                    |exec, _cclerk| {
                        starbridge_supply_chain_provenance::seed_item(exec, "manufacturer");
                    },
                    |app, sub| {
                        use starbridge_supply_chain_provenance as sc;
                        sc::fire_accept_custody(
                            app,
                            &sc::CUSTODIAN_RIGHTS,
                            sub.cipherclerk(),
                            sub.executor(),
                        )
                    },
                    |app, world| {
                        use starbridge_supply_chain_provenance as sc;
                        let item = app.cells()[0].cell();
                        // The custodian IS the firing principal (the agent cell's pubkey =
                        // the executor's `ctx.sender`). Mint the item TO that principal at
                        // genesis, so `SenderInSlot(CUSTODIAN)` holds on the seeded baton —
                        // exactly as `mint_effects_signed` binds the signer.
                        let custodian = app.cipherclerk().public_key().0;
                        let genesis_event =
                            sc::custody_event(&sc::GENESIS_PREV, &custodian, 1);
                        let genesis_link =
                            sc::link_hash(&sc::GENESIS_PREV, &genesis_event);
                        // SEED the minted item onto World: `item_program` (the custody policy:
                        // AnyOf[Immutable, SenderInSlot(CUSTODIAN)] + StrictMonotonic(EPOCH) +
                        // Monotonic(HEAD) + WriteOnce(links)) + the genesis baseline (CUSTODIAN
                        // = the firing principal, EPOCH=1, HEAD=1, link_0, TIP).
                        let spine = AppWorldSpine::seed(
                            world,
                            item,
                            custodian,
                            default_domain_token(),
                            sc::item_program(),
                            &[
                                SeedField {
                                    slot: sc::CUSTODIAN_SLOT as usize,
                                    value: custodian,
                                },
                                SeedField {
                                    slot: sc::EPOCH_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(1),
                                },
                                SeedField {
                                    slot: sc::link_slot(0),
                                    value: genesis_link,
                                },
                                SeedField {
                                    slot: sc::HEAD_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(1),
                                },
                                SeedField {
                                    slot: sc::TIP_SLOT as usize,
                                    value: genesis_link,
                                },
                            ],
                        );
                        // COMMIT `accept_custody` through World, AUTHENTICATED: the incoming
                        // holder takes the baton FOR ITSELF (CUSTODIAN := the firing principal,
                        // unchanged value), strictly advances EPOCH 1 → 2, appends link_1
                        // (WriteOnce), advances HEAD 1 → 2, points TIP. `SenderInSlot(CUSTODIAN)`
                        // holds because `ctx.sender` == the agent pubkey == the written CUSTODIAN.
                        // No witness blob needed (the clause reads `ctx.sender` directly).
                        let receipt = spine.commit_as(
                            custodian,
                            "accept_custody",
                            &sc::CUSTODIAN_RIGHTS,
                            &sc::CUSTODIAN_RIGHTS,
                            vec![],
                            |live| {
                                let from = live.fields[sc::CUSTODIAN_SLOT as usize];
                                let prev = live.fields[sc::TIP_SLOT as usize];
                                let event = sc::custody_event(&from, &custodian, 2);
                                let link = sc::link_hash(&prev, &event);
                                vec![
                                    dregg_app_framework::Effect::SetField {
                                        cell: item,
                                        index: sc::CUSTODIAN_SLOT as usize,
                                        value: custodian,
                                    },
                                    dregg_app_framework::Effect::SetField {
                                        cell: item,
                                        index: sc::EPOCH_SLOT as usize,
                                        value: dregg_app_framework::field_from_u64(2),
                                    },
                                    dregg_app_framework::Effect::SetField {
                                        cell: item,
                                        index: sc::link_slot(1),
                                        value: link,
                                    },
                                    dregg_app_framework::Effect::SetField {
                                        cell: item,
                                        index: sc::HEAD_SLOT as usize,
                                        value: dregg_app_framework::field_from_u64(2),
                                    },
                                    dregg_app_framework::Effect::SetField {
                                        cell: item,
                                        index: sc::TIP_SLOT as usize,
                                        value: link,
                                    },
                                ]
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "identity",
                    "Identity / Credentials",

                        "A credential issuer (issue → revoke) — an authorized issuer issues one credential, \
                         advancing the issuance sequence (the SenderAuthorized membership tooth bites).",
                    starbridge_identity::identity_app,
                    |exec, cclerk| {
                        starbridge_identity::seed_issuer(exec, cclerk, &starbridge_identity::kyc_schema());
                    },
                    |app, sub| {
                        use starbridge_identity as id;
                        id::fire_issue(app, &id::ISSUER_RIGHTS, sub.cipherclerk(), sub.executor())
                    },
                    |app, world| {
                        use starbridge_identity as id;
                        let issuer = app.cells()[0].cell();
                        // The authorized issuer IS the firing principal (agent pubkey =
                        // ctx.sender). Seed the auth root as the single-member set over THAT
                        // pubkey; the membership proof over the same pubkey clears
                        // `SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT })`.
                        let signer = app.cipherclerk().public_key().0;
                        let auth_root =
                            dregg_turn::executor::single_member_authorized_root(&signer);
                        let schema_hash =
                            id::schema_commitment(&id::kyc_schema());
                        // SEED onto World: `issuer_program` (WriteOnce SCHEMA + MonotonicSequence
                        // ISSUANCE_COUNTER + Monotonic REVOCATION_ROOT + SenderAuthorized) + the
                        // `seed_issuer` baseline (schema bound, counters 0, auth root = signer).
                        let spine = AppWorldSpine::seed(
                            world,
                            issuer,
                            signer,
                            default_domain_token(),
                            id::issuer_program(),
                            &[
                                SeedField {
                                    slot: id::SCHEMA_COMMITMENT_SLOT,
                                    value: schema_hash,
                                },
                                SeedField {
                                    slot: id::ISSUANCE_COUNTER_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: id::REVOCATION_ROOT_SLOT,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                                SeedField {
                                    slot: id::ISSUER_AUTH_ROOT_SLOT,
                                    value: auth_root,
                                },
                            ],
                        );
                        // COMMIT `issue` through World, AUTHENTICATED: advance the issuance
                        // counter +1 off live state (MonotonicSequence holds), CARRYING the
                        // single-member membership proof so the real MerkleMembership verifier
                        // admits the authorized signer (the SenderAuthorized tooth).
                        let witness =
                            dregg_turn::action::WitnessBlob::merkle_path(
                                dregg_turn::executor::single_member_membership_proof(&signer),
                            );
                        let receipt = spine.commit_as(
                            signer,
                            "issue",
                            &id::ISSUER_RIGHTS,
                            &id::ISSUER_RIGHTS,
                            vec![witness],
                            |live| {
                                let live_counter =
                                    field_tail_u64(&live.fields[id::ISSUANCE_COUNTER_SLOT]);
                                let new_counter = live_counter.saturating_add(1);
                                vec![
                                    dregg_app_framework::Effect::SetField {
                                        cell: issuer,
                                        index: id::ISSUANCE_COUNTER_SLOT,
                                        value: dregg_app_framework::field_from_u64(new_counter),
                                    },
                                    dregg_app_framework::Effect::EmitEvent {
                                        cell: issuer,
                                        event: dregg_app_framework::Event::new(
                                            dregg_app_framework::symbol("credential-issued"),
                                            vec![dregg_app_framework::field_from_u64(new_counter)],
                                        ),
                                    },
                                ]
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                AppEntry::framework(
                    "governed-namespace",
                    "Governed Namespace",

                        "A constitutionally-governed route table (propose → vote → commit) — a committee \
                         member opens a proposal, advancing the pending root (the SenderAuthorized committee tooth bites).",
                    starbridge_governed_namespace::governance_app,
                    |exec, _cclerk| {
                        use starbridge_governed_namespace as gn;
                        gn::seed_governance(
                            exec,
                            dregg_app_framework::field_from_bytes(b"committee-v0"),
                            2,
                            1,
                            dregg_app_framework::field_from_bytes(b"genesis-route-table-root"),
                        );
                    },
                    |app, sub| {
                        use starbridge_governed_namespace as gn;
                        gn::fire_propose(app, &gn::COMMITTEE_RIGHTS, sub.cipherclerk(), sub.executor())
                    },
                    |app, world| {
                        use starbridge_governed_namespace as gn;
                        let board = app.cells()[0].cell();
                        // The committee member IS the firing principal (agent pubkey =
                        // ctx.sender). Seed the committee root as the single-member set over
                        // THAT pubkey; the membership proof over the same pubkey clears
                        // `SenderAuthorized(PublicRoot { GOVERNANCE_COMMITTEE_ROOT_SLOT })`.
                        let signer = app.cipherclerk().public_key().0;
                        let committee_root =
                            dregg_turn::executor::single_member_authorized_root(&signer);
                        let route_table_root =
                            dregg_app_framework::field_from_bytes(b"genesis-route-table-root");
                        // SEED onto World: `governance_program` (the Cases program; the
                        // `propose_table_update` case binds Monotonic(PENDING) + SenderAuthorized)
                        // + the `seed_governance` baseline (committee root = signer, threshold,
                        // version=1, route table, PENDING=0).
                        let spine = AppWorldSpine::seed(
                            world,
                            board,
                            signer,
                            default_domain_token(),
                            gn::governance_program(),
                            &[
                                SeedField {
                                    slot: gn::GOVERNANCE_COMMITTEE_ROOT_SLOT as usize,
                                    value: committee_root,
                                },
                                SeedField {
                                    slot: gn::THRESHOLD_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(2),
                                },
                                SeedField {
                                    slot: gn::VERSION_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(1),
                                },
                                SeedField {
                                    slot: gn::ROUTE_TABLE_ROOT_SLOT as usize,
                                    value: route_table_root,
                                },
                                SeedField {
                                    slot: gn::PENDING_PROPOSAL_ROOT_SLOT as usize,
                                    value: dregg_app_framework::field_from_u64(0),
                                },
                            ],
                        );
                        // COMMIT `propose_table_update` through World, AUTHENTICATED: advance
                        // the pending root past its live value (Monotonic in the propose case),
                        // CARRYING the single-member membership proof so the real
                        // MerkleMembership verifier admits the committee member.
                        let witness =
                            dregg_turn::action::WitnessBlob::merkle_path(
                                dregg_turn::executor::single_member_membership_proof(&signer),
                            );
                        let receipt = spine.commit_as(
                            signer,
                            "propose_table_update",
                            &gn::COMMITTEE_RIGHTS,
                            &gn::COMMITTEE_RIGHTS,
                            vec![witness],
                            |live| {
                                let pending = field_tail_u64(
                                    &live.fields[gn::PENDING_PROPOSAL_ROOT_SLOT as usize],
                                );
                                let new_pending =
                                    dregg_app_framework::field_from_u64(pending.saturating_add(1));
                                vec![
                                    dregg_app_framework::Effect::SetField {
                                        cell: board,
                                        index: gn::PENDING_PROPOSAL_ROOT_SLOT as usize,
                                        value: new_pending,
                                    },
                                    dregg_app_framework::Effect::EmitEvent {
                                        cell: board,
                                        event: dregg_app_framework::Event::new(
                                            dregg_app_framework::symbol("proposal-opened"),
                                            vec![new_pending],
                                        ),
                                    },
                                ]
                            },
                        )?;
                        Ok((spine, receipt))
                    }
                ),
                // ───────────────────────────────────────────────────────────
                // THE POLIS GOVERNANCE LAYER — a PROGRAM entry, not a `DeosApp`.
                // `starbridge-polis` ships per-charter content-addressed
                // `CellProgram`s directly (`council::council_cell_program(charter)`),
                // so its World drive needs no framework app: it installs a council
                // governance cell carrying that program onto `World` via
                // `AppWorldSpine::seed` (birth state DRAFT, all-zero — no seed
                // fields), then fires ONE representative governance affordance — a
                // council `propose` — through `AppWorldSpine::commit`. The propose
                // turn steps STATE 0 (DRAFT) → 1 (PROPOSED), writes the staged
                // proposal hash (WriteOnce) and pins the membership commitment (the
                // `pin_term` that bites once the cell leaves DRAFT). The legacy
                // `CouncilCharter::new` charter carries NO `member_keys`, so there is
                // NO `SenderIs`/`SenderAuthorized` clause — the single-custody
                // `commit` path suffices (no witness blob, no `commit_as`). World's
                // executor RE-ENFORCES the full council program on commit, so a
                // committed receipt proves the governance state machine accepted the
                // proposal.
                #[cfg(feature = "embedded-executor")]
                AppEntry::program(
                    "polis",
                    "Polis Council",
                    "A constitutional council (M-of-N proposal governance) — a member opens a \
                     proposal, advancing the council cell DRAFT → PROPOSED (the membership \
                     commitment pins + the staged-proposal WriteOnce tooth bite).",
                    |world| {
                        use starbridge_polis::council;
                        // A small real charter: a 2-of-3 council over three synthetic
                        // member cells. The charter is content-addressed into the
                        // installed program; its membership commitment is the literal
                        // the cell pins once it leaves DRAFT.
                        let members: Vec<dregg_cell::CellId> = (1u8..=3)
                            .map(|i| dregg_cell::CellId::from_bytes([i; 32]))
                            .collect();
                        let charter = council::CouncilCharter::new(members, 2);
                        let program = council::council_cell_program(&charter)
                            .map_err(|e| WorldFireError::World {
                                reason: format!("polis charter refused to build: {e}"),
                            })?;
                        // The governance cell is born in DRAFT (state 0, every slot
                        // zero) — exactly the default genesis cell — so NO seed fields
                        // are needed. The agent/pubkey is a fixed governance-operator
                        // key (the single-custody operator that opens the proposal).
                        let operator_pk = [0x90u8; 32];
                        let spine = AppWorldSpine::seed(
                            Rc::clone(&world),
                            dregg_cell::Cell::with_balance(
                                operator_pk,
                                default_domain_token(),
                                1_000_000,
                            )
                            .id(),
                            operator_pk,
                            default_domain_token(),
                            program,
                            &[],
                        );
                        let gov_cell = spine.app_cell();
                        // COMMIT `propose` through World: DRAFT(0) → PROPOSED(1),
                        // staging a proposal hash (WriteOnce) and publishing the
                        // membership commitment (`pin_term` — required once out of
                        // DRAFT). No sender clause on a legacy charter, so the
                        // single-custody `commit` admits it; World's executor
                        // re-enforces the council machine.
                        let proposal_hash =
                            dregg_app_framework::field_from_u64(0x90_0_5A1);
                        let members_commit = charter.members_commitment();
                        let receipt = spine.commit(
                            "propose",
                            &AuthRequired::None,
                            &AuthRequired::None,
                            |_live| {
                                vec![
                                    dregg_app_framework::Effect::SetField {
                                        cell: gov_cell,
                                        index: starbridge_polis::STATE_SLOT as usize,
                                        value: dregg_app_framework::field_from_u64(
                                            council::STATE_PROPOSED,
                                        ),
                                    },
                                    dregg_app_framework::Effect::SetField {
                                        cell: gov_cell,
                                        index: council::PROPOSAL_HASH_SLOT as usize,
                                        value: proposal_hash,
                                    },
                                    dregg_app_framework::Effect::SetField {
                                        cell: gov_cell,
                                        index: council::MEMBERS_COMMIT_SLOT as usize,
                                        value: members_commit,
                                    },
                                ]
                            },
                        )?;
                        Ok((spine, receipt))
                    },
                )
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

    /// **Launch the app with id `id`** over the app-framework substrate, in
    /// `federation` — the cockpit's launcher entry point. `None` if no entry has that
    /// id, OR if the entry is a PROGRAM entry (polis) with no framework-substrate path
    /// (launch such an entry onto the cockpit `World` with
    /// [`AppRegistry::launch_on_world`]).
    pub fn launch(&self, id: &str, federation: [u8; 32]) -> Option<LaunchedRegistryApp> {
        self.get(id).and_then(|e| e.launch(federation))
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
        // The second wave (wired onto the live World ledger).
        for id in [
            "agent-orchestration",
            "agent-provenance",
            "compartment-workflow-mandate",
            "compute-exchange",
            "escrow-market",
            "nameservice",
            "privacy-voting",
            "storage-gateway-mandate",
            "subscription",
            "swarm-orchestration",
            "tool-access-delegation",
            // The sender-bound wave.
            "supply-chain-provenance",
            "identity",
            "governed-namespace",
        ] {
            assert!(
                ids.contains(&id),
                "{id} is wired into the standard registry"
            );
        }
        // The polis governance layer — a PROGRAM entry (not a `DeosApp`).
        #[cfg(feature = "embedded-executor")]
        assert!(
            ids.contains(&"polis"),
            "polis (the council governance program) is wired into the standard registry"
        );
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
            // PROGRAM entries (polis) have no framework-substrate path — `launch`
            // returns `None`. They are exercised by the World-path whole-set test
            // (`every_wired_app_launches_on_the_cockpit_world`) instead.
            let Some(launched) = entry.launch(federation) else {
                continue;
            };
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
            assert!(
                launched.receipt.action_count >= 1,
                "{} fired an action",
                entry.id
            );
        }
    }

    /// **THE SENDER-BOUND PROOF** — the three sender-reading apps launch on World AND
    /// their committed turn GENUINELY carried the sender. The proof is by REFUTATION:
    /// the affordance's installed program clause reads `ctx.sender` (supply-chain's
    /// `SenderInSlot(CUSTODIAN)`, identity's + governed-namespace's `SenderAuthorized`),
    /// and the executor re-enforces it on commit. If the sender were absent (the bare
    /// `Unchecked` path with no agent-pubkey sender), the clause would surface
    /// `MissingContextField` and the turn would be REJECTED. A COMMITTED receipt on
    /// `World::receipts()` therefore proves the sender clause was SATISFIED — i.e. the
    /// turn carried the sender the seeded slot/root commits to.
    #[cfg(feature = "embedded-executor")]
    #[test]
    fn the_sender_bound_apps_carry_their_sender_onto_world() {
        let reg = AppRegistry::standard();
        for id in ["supply-chain-provenance", "identity", "governed-namespace"] {
            let world = Rc::new(RefCell::new(World::new()));
            let receipts_before = world.borrow().receipts().len();
            let launched = reg
                .launch_on_world(id, [0xABu8; 32], Rc::clone(&world))
                .unwrap_or_else(|| panic!("{id} is in the standard registry"))
                .unwrap_or_else(|e| panic!("{id} commits its sender-bound turn onto World: {e}"));
            let app_cell = launched.primary_cell();

            // The cell is on the cockpit World ledger.
            assert!(
                world.borrow().ledger().get(&app_cell).is_some(),
                "{id} cell is on the cockpit World ledger"
            );
            // ONE receipt landed in World::receipts() — and because the installed program
            // clause reads ctx.sender, this committed receipt PROVES the sender was carried
            // (a missing sender would have been a MissingContextField rejection).
            assert_eq!(
                world.borrow().receipts().len(),
                receipts_before + 1,
                "{id} committed its sender-bound turn (sender clause satisfied ⇒ sender carried)"
            );
            assert_eq!(
                launched.receipt.agent, app_cell,
                "{id} World receipt is authored by the app cell"
            );
            assert!(launched.receipt.action_count >= 1, "{id} fired an action");
        }
    }

    /// **THE POLIS GOVERNANCE PROOF** — launch the polis council PROGRAM entry onto a
    /// cockpit `World`, fire its representative governance affordance (a council
    /// `propose`), and assert the council cell lands on `World::ledger()` advanced to
    /// PROPOSED AND its receipt on `World::receipts()` — the REAL cockpit inspector
    /// path. Polis is NOT a `DeosApp` (it ships a `CellProgram` directly), so this also
    /// proves the program-backend registry path works. DONE = this RAN.
    ///
    /// This is also a proof-by-refutation that the governance state machine accepted
    /// the proposal: World's executor RE-ENFORCES the full council program on commit
    /// (the `AllowedTransitions` DRAFT→PROPOSED row, the `WriteOnce` proposal hash, the
    /// `pin_term` membership commitment that bites the instant the cell leaves DRAFT).
    /// A malformed propose (wrong commitment, a skipped slot) would be REJECTED, so a
    /// committed receipt proves the council machine admitted the step.
    #[cfg(feature = "embedded-executor")]
    #[test]
    fn launching_polis_council_commits_a_propose_turn_to_the_cockpit_world() {
        use starbridge_polis::council;

        let world = Rc::new(RefCell::new(World::new()));
        let receipts_before = world.borrow().receipts().len();
        let cells_before = world.borrow().cell_count();

        let reg = AppRegistry::standard();
        let launched = reg
            .launch_on_world("polis", [0xC0u8; 32], Rc::clone(&world))
            .expect("polis is in the standard registry")
            .expect("polis seeds a council cell + commits a propose turn onto the live World");

        // Polis is a PROGRAM entry — no `DeosApp`.
        assert!(
            launched.app.is_none(),
            "the polis entry is a program backend (no DeosApp)"
        );

        let gov_cell = launched.primary_cell();

        // THE COCKPIT INSPECTOR PATH (World::ledger): the council cell is on the live
        // World ledger, advanced to PROPOSED by the committed propose turn.
        let cell_on_world = world
            .borrow()
            .ledger()
            .get(&gov_cell)
            .cloned()
            .expect("the council cell is on the cockpit World ledger (genesis-installed)");
        assert_eq!(
            world.borrow().cell_count(),
            cells_before + 1,
            "the council cell was added to the cockpit World"
        );

        // The STATE slot reads PROPOSED (1) — the governance machine stepped DRAFT → PROPOSED.
        let state_tail = {
            let f = &cell_on_world.state.fields[starbridge_polis::STATE_SLOT as usize];
            let mut b = [0u8; 8];
            b.copy_from_slice(&f[24..32]);
            u64::from_be_bytes(b)
        };
        assert_eq!(
            state_tail,
            council::STATE_PROPOSED,
            "the council cell advanced DRAFT → PROPOSED on the cockpit World"
        );
        // The membership commitment slot is non-zero (the `pin_term` published it on leaving DRAFT).
        assert_ne!(
            cell_on_world.state.fields[council::MEMBERS_COMMIT_SLOT as usize],
            [0u8; 32],
            "the membership commitment was published on the World cell"
        );

        // THE COCKPIT INSPECTOR PATH (World::receipts): the receipt is in World's OWN log.
        assert_eq!(
            launched.receipt.agent, gov_cell,
            "the World-committed propose turn is authored by the council cell"
        );
        assert!(launched.receipt.action_count >= 1);
        assert_eq!(
            world.borrow().receipts().len(),
            receipts_before + 1,
            "the propose fire landed ONE receipt in World::receipts()"
        );
    }
}
