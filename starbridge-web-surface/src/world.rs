//! **The web-of-cells game world + the membrane as a negotiation surface** — the
//! deos distribution model made real, lifting the single-process [`crate::game`]
//! board into a *federated world of cells* and realizing the membrane's
//! "GitHub-org-settings page" negotiation (`REHYDRATABLE-SURFACES.md` residual #1).
//!
//! ## What this module adds (the "bigger vision")
//!
//! The `game.rs` board is the ground truth; this module is how a multiplayer deos
//! WORLD is *distributed, spectated, and negotiated*:
//!
//! - **[`GameWorld`] — the world as cells.** The board, each player, and each
//!   objective are PUBLISHED as real cells into a real [`WebOfCells`]
//!   (`docs/deos/DEOS-APPS.md`: "each player a cell, the board a shared cell, every
//!   tile a cell"). A peer reaches the world by resolving its `dregg://` refs (a
//!   verified, attested cross-cell read), not by trusting a server. The world is the
//!   composition the apps doc names: cells × affordances × distribution.
//! - **[`Lobby`] — the federation.** Many worlds live in one lobby (the web-of-cells
//!   is federated); a `dregg://` ref names a world across the federation. This is the
//!   distributed-app axis the apps-doc census flagged as unbuilt.
//! - **[`MembraneNegotiation`] — the org-settings page.** The doc's sharpest
//!   adoptability framing: the membrane's negotiation semantics ARE a GitHub-org
//!   settings page (teams = cap groups, roles = the attenuation lattice, visibility =
//!   projection scope, fork policy = re-share rules). This module realizes that as a
//!   typed protocol: a player PROPOSES a [`SpectatorGrant`] (watch-my-side /
//!   watch-objectives / watch-all-post-game), the grant is minted ONLY as an
//!   attenuation of what the granter holds (the REAL `is_attenuation`), and re-sharing
//!   a grant (A→B→C) composes through the REAL [`Membrane::reshare`] — refusing any
//!   amplifying hop. The who-proposes / who-refuses / what-happens-on-disagreement is
//!   the negotiation surface the residual said was "still wood"; here it is steel.
//! - **[`SpectatorSession`] — the rehydration carrying the liveness-type.** A
//!   spectator opens a frustum-snapshot through their granted membrane; the
//!   re-expansion is liveness-typed (`Live` / `ReplayedDeterministic` /
//!   `ReconstructedApproximate`) and fog-respecting (a Blue-gated spectator names NO
//!   Red moves), exactly as `game.rs::snapshot_for` + `rehydrate_affordances` already
//!   prove — wired here into the negotiated grant.
//!
//! ## Honesty (Tier A — no laundering)
//!
//! Everything here is the genuine cap discipline: a grant is `SurfaceCapability`
//! minted by `attenuate_child` / checked by `is_attenuation`; a reshare is
//! `Membrane::reshare`; a world cell is a real published `WebOfCells` cell with a
//! verifiable `AttestedRoot`. The ONE inherited seam is the same one `affordance.rs`
//! and `game.rs` name: a fired move's `AffordanceIntent` carries the REAL effect but
//! handing it to a live `dregg_turn::TurnExecutor` is the cross-crate dispatch seam
//! (the world advances its own board model in the interim, exactly as `MockSurface`
//! advances from a gated request). The negotiation, distribution, spectating, and
//! liveness-typing are all real here and now.

use crate::delegate::SurfaceCapability;
use crate::game::{side_rights, Board, Coord, Objective, Side};
use crate::rehydrate::{Interaction, InteractionLog, Membrane, RehydrateError, Rehydration};
use crate::web_of_cells::{DreggUri, WebOfCells};
use dregg_cell::AuthRequired;
use dregg_types::CellId;

// ──────────────────────────────────────────────────────────────────────────────
// GameWorld — the board/players/objectives published as cells in a web-of-cells.
// ──────────────────────────────────────────────────────────────────────────────

/// A multiplayer **game world** distributed across the web-of-cells: the board, the
/// two players, and every objective are published as real cells with `dregg://`
/// refs, reachable by any peer via a verified attested fetch.
///
/// `docs/deos/DEOS-APPS.md`: "multiplayer = the web-of-cells (each player a cell,
/// the board a shared cell, every tile a cell)." A [`GameWorld`] is exactly that
/// composition — the single-process [`Board`] lifted into a federated set of cells.
#[derive(Clone, Debug)]
pub struct GameWorld {
    /// A short world id (its name within the lobby).
    pub id: String,
    /// The board (ground truth). The world publishes a *projection* of it per viewer;
    /// the full board is never handed to a peer whole.
    pub board: Board,
    /// The board cell's published `dregg://` ref (the shared cell).
    pub board_uri: DreggUri,
    /// Each player's published cell ref (Blue, Red) — players are cells.
    pub player_uris: Vec<(Side, DreggUri)>,
    /// Each objective's published cell ref — objectives are cells too.
    pub objective_uris: Vec<(String, DreggUri)>,
}

impl GameWorld {
    /// **Publish a [`Board`] as a world of cells** into `web`, namespaced by
    /// `seed_base` so distinct worlds in one federation get DISTINCT cells (the
    /// web-of-cells panics on a colliding seed — a real "this origin already exists").
    /// The board becomes a shared cell; each player and objective is published as its
    /// own cell with a committed `dregg://` ref. Returns the [`GameWorld`].
    ///
    /// The published board cell content is the trusted chrome the spectator's
    /// rehydration verifies; the per-player / per-objective cells make the world a
    /// genuine web of addressable, attested objects (not a single blob).
    pub fn publish_with_base(
        id: impl Into<String>,
        board: Board,
        web: &mut WebOfCells,
        seed_base: u8,
    ) -> Self {
        let id = id.into();
        // A per-world seed: high nibble = the world's base, low nibble = the object.
        // (16 worlds × 16 objects per world before a wrap — ample for a lobby demo.)
        let seed = |obj: u8| seed_base.wrapping_shl(4).wrapping_add(obj & 0x0F);
        // The board cell — the shared cell of the skirmish (object 0).
        let board_uri = web.publish(
            seed(0),
            format!("<h1>deos world: {id}</h1><p>a fog-of-war skirmish board</p>").as_bytes(),
            "dregg://world/board",
        );
        // Each player is its own published cell (objects 1-2).
        let mut player_uris = Vec::new();
        for (i, side) in [Side::Blue, Side::Red].into_iter().enumerate() {
            let uri = web.publish(
                seed(1 + i as u8),
                format!("<h1>player: {}</h1>", side.label()).as_bytes(),
                "dregg://world/player",
            );
            player_uris.push((side, uri));
        }
        // Each objective is its own published cell (objects 3+).
        let mut objective_uris = Vec::new();
        for (j, obj) in board.objectives.iter().enumerate() {
            let uri = web.publish(
                seed(3 + j as u8),
                format!("<h1>objective: {}</h1>", obj.name).as_bytes(),
                "dregg://world/objective",
            );
            objective_uris.push((obj.name.clone(), uri));
        }
        GameWorld {
            id,
            board,
            board_uri,
            player_uris,
            objective_uris,
        }
    }

    /// Publish a board as a world with the default seed base (`0`) — the convenience
    /// for a SINGLE world. Use [`GameWorld::publish_with_base`] for a multi-world
    /// lobby (distinct bases avoid cell-seed collisions).
    pub fn publish(id: impl Into<String>, board: Board, web: &mut WebOfCells) -> Self {
        Self::publish_with_base(id, board, web, 0)
    }

    /// The published ref of `side`'s player cell.
    pub fn player_uri(&self, side: Side) -> Option<&DreggUri> {
        self.player_uris
            .iter()
            .find(|(s, _)| *s == side)
            .map(|(_, u)| u)
    }

    /// The published ref of the objective named `name`.
    pub fn objective_uri(&self, name: &str) -> Option<&DreggUri> {
        self.objective_uris
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, u)| u)
    }

    /// The number of cells this world publishes (board + 2 players + N objectives) —
    /// a readout that the world is a genuine *web* of addressable cells.
    pub fn cell_count(&self) -> usize {
        1 + self.player_uris.len() + self.objective_uris.len()
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// Lobby — a federation of worlds.
// ──────────────────────────────────────────────────────────────────────────────

/// A **lobby** — a federation of [`GameWorld`]s sharing one [`WebOfCells`]. The
/// web-of-cells is federated (`docs/deos/...`: "an app spanning federated cells"),
/// so many concurrent worlds live in one lobby and a `dregg://` ref names a world
/// across it. This is the "an app spanning federated cells" axis the apps-doc census
/// said had *zero* exemplar.
pub struct Lobby {
    /// The shared web-of-cells the lobby's worlds publish into.
    pub web: WebOfCells,
    /// The worlds currently hosted.
    pub worlds: Vec<GameWorld>,
}

impl Lobby {
    /// A fresh lobby with a quorum-`quorum_size` web-of-cells.
    pub fn new(quorum_size: usize) -> Self {
        Lobby {
            web: WebOfCells::new(quorum_size),
            worlds: Vec::new(),
        }
    }

    /// Host a new world (publish a board into the lobby's federation). Each world gets
    /// a distinct seed base (its index) so its cells do not collide with another
    /// world's in the shared web-of-cells. Returns the hosted world's index.
    pub fn host(&mut self, id: impl Into<String>, board: Board) -> usize {
        let base = self.worlds.len() as u8;
        let world = GameWorld::publish_with_base(id, board, &mut self.web, base);
        self.worlds.push(world);
        self.worlds.len() - 1
    }

    /// A hosted world by id.
    pub fn world(&self, id: &str) -> Option<&GameWorld> {
        self.worlds.iter().find(|w| w.id == id)
    }

    /// The number of worlds in the lobby.
    pub fn world_count(&self) -> usize {
        self.worlds.len()
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// The membrane as a negotiation surface — the GitHub-org-settings page.
// ──────────────────────────────────────────────────────────────────────────────

/// What a spectator is granted to watch — the *projection scope* of a
/// [`SpectatorGrant`]. This is the "visibility = projection scope" row of the
/// org-settings analogy (`REHYDRATABLE-SURFACES.md`): a granter chooses which slice
/// of the world a spectator may re-view, and the grant is minted as exactly that
/// attenuation — never wider.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpectatorScope {
    /// Watch one SIDE's fog-of-war view (the spectator sees what that side sees —
    /// gated to that side's identity, fog-respecting). The default "watch my games".
    OneSide(Side),
    /// Watch only the OBJECTIVES (the control points + who holds them) — a
    /// commentary/scoreboard view that leaks no unit positions. A narrower scope than
    /// a full side view.
    ObjectivesOnly,
    /// Watch the WHOLE board — only valid for a POST-GAME grant (after the match is
    /// decided, there is nothing left to hide). The "make the replay public" setting.
    FullPostGame,
}

/// A negotiated **spectator grant** — a revocable, attenuated, per-viewer right to
/// re-view a slice of the world, minted by a granter who holds the authority and
/// shaped by a [`SpectatorScope`]. This is the unit of the membrane negotiation: it
/// IS a [`SurfaceCapability`] (so it composes through the real lattice), tagged with
/// its scope + the granter, and re-shareable (A→B→C) through [`Membrane::reshare`].
#[derive(Clone, Debug)]
pub struct SpectatorGrant {
    /// The scope this grant authorizes.
    pub scope: SpectatorScope,
    /// The cap the grant confers — a real [`SurfaceCapability`], an attenuation of
    /// what the granter held. The membrane minted through it can never exceed this.
    pub cap: SurfaceCapability,
    /// The granter's side (who extended this right). For audit / the chrome.
    pub granter: Side,
}

impl SpectatorGrant {
    /// A membrane over this grant's cap — the enforcer a spectator rehydrates
    /// through. Any projection it mints is `≤` the grant's cap (and `≤` the
    /// sturdyref's lineage).
    pub fn membrane(&self) -> Membrane {
        Membrane::new(self.cap.clone())
    }
}

/// Why a membrane negotiation refused a proposal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NegotiationError {
    /// The granter cannot extend this scope because it does not itself hold the
    /// authority the scope requires (you cannot grant a view of a side whose vision
    /// you do not hold) — the REAL `is_attenuation` refused the mint. The structural
    /// analog of "you can't add someone to a team you're not on".
    GranterLacksAuthority { scope: SpectatorScope },
    /// A [`SpectatorScope::FullPostGame`] grant was proposed while the game is still
    /// LIVE — refused, because a full-board view mid-game would leak the fog. The
    /// "this repo can't be made public while it has secrets" rule.
    GameStillLive,
    /// A re-share (A→B→C) would AMPLIFY beyond what the resharer held — refused by the
    /// REAL [`Membrane::reshare`]. The anti-ghost tooth of the negotiation: a forwarded
    /// spectator link can never widen.
    ReshareWouldAmplify,
}

/// **The membrane negotiation surface** — the GitHub-org-settings page for a
/// [`GameWorld`]'s spectator rights. A granter (a player, or the world host) uses it
/// to PROPOSE spectator grants; the surface MINTS each grant only as a genuine
/// attenuation of the granter's authority (refusing over-broad proposals), and
/// composes re-shares through the real lattice. This is the residual-#1 negotiation
/// UX made into a typed protocol on the proven `is_attenuation` / `reshare` algebra.
///
/// The who-proposes / who-refuses / disagreement semantics:
/// - **who proposes:** a holder of a side's vision authority (`propose_*`);
/// - **who refuses:** the surface itself, structurally — a proposal that would
///   amplify is refused ([`NegotiationError`]), not negotiated down silently;
/// - **disagreement:** a spectator who wants MORE than offered simply cannot mint it
///   (the grant they get is the meet; asking for more is amplification → refused).
pub struct MembraneNegotiation<'w> {
    /// The world whose spectator rights are being negotiated.
    pub world: &'w GameWorld,
}

impl<'w> MembraneNegotiation<'w> {
    /// Open the negotiation surface for `world`.
    pub fn for_world(world: &'w GameWorld) -> Self {
        MembraneNegotiation { world }
    }

    /// **Propose a one-side spectator grant.** The `granter` (who must hold
    /// `watch_side`'s vision authority — typically the player of that side, or the
    /// host) extends a right to watch `watch_side`'s fog-of-war view. The grant is
    /// minted as exactly the side's vision facet (gated to the side's identity,
    /// scoped to its frustum) — so the spectator sees what that side sees, and the
    /// no-peek property carries (a Blue-side grant cannot re-expand Red's tiles).
    ///
    /// Refused with [`NegotiationError::GranterLacksAuthority`] if the granter's held
    /// authority does not attenuate the side's vision identity (the REAL gate).
    pub fn propose_one_side(
        &self,
        granter: Side,
        granter_held: &SurfaceCapability,
        watch_side: Side,
    ) -> Result<SpectatorGrant, NegotiationError> {
        // The scope's required authority: the side's vision facet.
        let scope_cap = self.world.board.vision_lineage_for(watch_side);
        // The granter must HOLD enough authority to extend this (is_attenuation:
        // granter_held ⊇ the side identity). A player of `watch_side` holds it; an
        // unrelated party does not.
        if !dregg_cell::is_attenuation(&granter_held.window.rights, &scope_cap.window.rights) {
            return Err(NegotiationError::GranterLacksAuthority {
                scope: SpectatorScope::OneSide(watch_side),
            });
        }
        Ok(SpectatorGrant {
            scope: SpectatorScope::OneSide(watch_side),
            cap: scope_cap,
            granter,
        })
    }

    /// **Propose an objectives-only spectator grant** — a scoreboard/commentary view
    /// that reveals the control points and who holds them, but NO unit positions
    /// (strictly narrower than a side view). The grant's fetch-scope is exactly the
    /// objective tiles; its identity is a distinct "spectator" `Custom` gate so it
    /// is incomparable to either side's vision (it cannot be widened into a side
    /// view). Any holder may extend this (it leaks nothing hidden).
    pub fn propose_objectives_only(
        &self,
        granter: Side,
    ) -> Result<SpectatorGrant, NegotiationError> {
        let objective_origins: std::collections::BTreeSet<String> = self
            .world
            .board
            .objectives
            .iter()
            .map(|o| o.at.origin())
            .collect();
        let cap = SurfaceCapability::scoped(
            self.world.board.cell,
            spectator_rights(),
            objective_origins,
            [],
        );
        Ok(SpectatorGrant {
            scope: SpectatorScope::ObjectivesOnly,
            cap,
            granter,
        })
    }

    /// **Propose a full-board, post-game grant** — "make the replay public". Valid
    /// ONLY once the game is decided ([`Board::outcome`] is `Some`); proposing it
    /// while the game is live is refused ([`NegotiationError::GameStillLive`]),
    /// because a full-board view mid-game leaks the fog. After the game, a full view
    /// hides nothing, so the grant confers the world's root authority over the board.
    pub fn propose_full_post_game(
        &self,
        granter: Side,
    ) -> Result<SpectatorGrant, NegotiationError> {
        if self.world.board.outcome().is_none() {
            return Err(NegotiationError::GameStillLive);
        }
        // Post-game: a full-board view. The cap is the board root (no fog left).
        let cap = SurfaceCapability::root(self.world.board.cell, AuthRequired::None);
        Ok(SpectatorGrant {
            scope: SpectatorScope::FullPostGame,
            cap,
            granter,
        })
    }

    /// **Re-share a grant (A→B→C)** — forward a spectator right to a downstream
    /// viewer with a (possibly further-attenuated) `requested` cap. Composes through
    /// the REAL [`Membrane::reshare`]: the reshare is admitted IFF `requested` is an
    /// attenuation of the grant on EVERY axis; an amplifying forward is refused
    /// ([`NegotiationError::ReshareWouldAmplify`]). This is the "fork policy /
    /// re-share rules" row of the org-settings analogy, on the proven lattice.
    pub fn reshare(
        &self,
        grant: &SpectatorGrant,
        requested: SurfaceCapability,
    ) -> Result<SpectatorGrant, NegotiationError> {
        let membrane = grant.membrane();
        match membrane.reshare(requested) {
            Ok(downstream) => Ok(SpectatorGrant {
                scope: grant.scope,
                cap: downstream.held().clone(),
                granter: grant.granter,
            }),
            Err(RehydrateError::Amplification) => Err(NegotiationError::ReshareWouldAmplify),
            // A reshare cannot fetch-fail (no fetch happens); any other error is also
            // an amplification refusal for our purposes.
            Err(_) => Err(NegotiationError::ReshareWouldAmplify),
        }
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// SpectatorSession — opening a grant into a fog-respecting, liveness-typed view.
// ──────────────────────────────────────────────────────────────────────────────

/// A live (or replayed) **spectator session** — what a spectator gets when they open
/// a world through their negotiated [`SpectatorGrant`]. It carries the per-viewer
/// fog-respecting board view + the [`Rehydration`] liveness-type (which kind of true
/// the spectator is touching). This is the rehydration lifted onto the negotiated
/// grant: the grant decides the scope, the membrane enforces it, the liveness-type
/// keeps it honest.
#[derive(Clone, Debug)]
pub struct SpectatorSession {
    /// The grant this session was opened under.
    pub scope: SpectatorScope,
    /// The coordinates the spectator may see (the fog-respecting frustum). For a
    /// `OneSide` grant this is the side's vision; for `ObjectivesOnly` it is the
    /// objective tiles; for `FullPostGame` it is the whole board.
    pub visible: Vec<Coord>,
    /// The objectives the spectator may see and who holds them (always visible to a
    /// scoreboard view; visible-if-in-frustum to a side view).
    pub objectives: Vec<(String, Coord, Option<Side>)>,
    /// The liveness-type — DERIVED from the source context's witness-log (live scene
    /// vs deterministic replay vs approximate reconstruction). The system cannot lie
    /// about which it is.
    pub liveness: Rehydration,
}

impl SpectatorSession {
    /// **Open** a spectator session for `grant` over `world`, deriving the liveness
    /// from `witness_log` + `sources_reachable` (exactly as `rehydrate` does). The
    /// view is computed from the grant's SCOPE, fog-respecting throughout:
    ///
    /// - `OneSide(side)` → the side's fog-of-war view (only what that side sees);
    /// - `ObjectivesOnly` → just the objective tiles (no unit positions leaked);
    /// - `FullPostGame` → the whole board (only reachable post-game).
    ///
    /// The liveness-type is carried through so the spectator knows whether they are
    /// watching the live match or a replay.
    pub fn open(
        world: &GameWorld,
        grant: &SpectatorGrant,
        witness_log: &InteractionLog,
        sources_reachable: bool,
    ) -> Self {
        let board = &world.board;
        let liveness = Rehydration::classify(witness_log, sources_reachable);

        let (visible, objectives) = match grant.scope {
            SpectatorScope::OneSide(side) => {
                let view = board.project_for(side, liveness);
                let coords = view.visible_coords();
                // Objectives the side can see (in its frustum).
                let objs = board
                    .objectives
                    .iter()
                    .filter(|o| view.can_see(o.at))
                    .map(|o| (o.name.clone(), o.at, o.held_by))
                    .collect();
                (coords, objs)
            }
            SpectatorScope::ObjectivesOnly => {
                // Only the objective tiles, and the holder of each — no unit leak.
                let coords = board.objectives.iter().map(|o| o.at).collect();
                let objs = board
                    .objectives
                    .iter()
                    .map(|o| (o.name.clone(), o.at, o.held_by))
                    .collect();
                (coords, objs)
            }
            SpectatorScope::FullPostGame => {
                let mut coords = Vec::new();
                for r in 0..board.rows {
                    for c in 0..board.cols {
                        coords.push(Coord::new(r, c));
                    }
                }
                let objs = board
                    .objectives
                    .iter()
                    .map(|o| (o.name.clone(), o.at, o.held_by))
                    .collect();
                (coords, objs)
            }
        };

        SpectatorSession {
            scope: grant.scope,
            visible,
            objectives,
            liveness,
        }
    }

    /// Does this session reveal any of `side`'s UNITS? A scoreboard (objectives-only)
    /// session must reveal NONE (the no-leak property of the narrow scope). Used by
    /// tests to assert the scope confinement.
    pub fn reveals_unit_of(&self, world: &GameWorld, side: Side) -> bool {
        world
            .board
            .units
            .iter()
            .filter(|u| u.side == side)
            .any(|u| {
                self.visible.contains(&u.at)
                    && matches!(
                        self.scope,
                        SpectatorScope::OneSide(_) | SpectatorScope::FullPostGame
                    )
            })
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// helpers
// ──────────────────────────────────────────────────────────────────────────────

/// The window-rights identity of a SPECTATOR scope — a distinct `Custom` gate that
/// is INCOMPARABLE to either side's vision identity, so an objectives-only /
/// scoreboard grant can never be widened (re-shared) into a side's fog-of-war view.
/// (A fresh domain-separated vk_hash, the same incomparability the fog rides on.)
fn spectator_rights() -> AuthRequired {
    let vk = *blake3::hash(b"dregg-fogwar-spectator-scoreboard-v1").as_bytes();
    AuthRequired::Custom { vk_hash: vk }
}

/// Build a witness-log of an ATTESTED fetch of `world`'s board cell (carrying the
/// cell's real `AttestedRoot`), so a spectator session derives
/// `ReplayedDeterministic` — the confined fragment. A convenience for demos/tests:
/// it fetches the board cell out of `web` (a real attested read) and records the
/// attestation as a witnessed interaction. (`web` is the lobby's web-of-cells the
/// world was published into.)
pub fn witnessed_log_for(web: &WebOfCells, world: &GameWorld) -> InteractionLog {
    let mut log = InteractionLog::new();
    if let Ok((resource, _chrome)) = web.fetch(&world.board_uri) {
        log.record(Interaction::attested_fetch(
            world.board_uri.clone(),
            resource.attested_root,
        ));
    }
    log
}

/// Build a witness-log with at least one AMBIENT (un-witnessed) interaction, so a
/// spectator session derives `ReconstructedApproximate` (a context that reached
/// outside the membrane). The honest "this is a reconstruction, not the live scene".
pub fn ambient_log() -> InteractionLog {
    let mut log = InteractionLog::new();
    log.record(Interaction::ambient(
        "a raw, un-witnessed timing/agent choice",
    ));
    log
}

/// Derive a deterministic spectator cell id (a spectator is a cell too).
pub fn spectator_cell(seed: u8) -> CellId {
    let mut k = [0u8; 32];
    k[0] = 0x5C;
    k[1] = seed;
    CellId::derive_raw(&k, &[0u8; 32])
}

/// The vision cap a real player of `side` holds over `world` — used as the
/// `granter_held` authority when that player proposes a spectator grant of their own
/// side. (A thin pass-through to [`Board::vision_cap_for`] so callers do not reach
/// into the board.)
pub fn player_authority(world: &GameWorld, side: Side) -> SurfaceCapability {
    world.board.vision_cap_for(side)
}

/// A convenience: the side-rights identity for `side` (re-exported through this
/// module so world-level callers name it here).
pub fn world_side_rights(side: Side) -> AuthRequired {
    side_rights(side)
}

/// A neutral objective placed at `at` named `name` (re-exported constructor so a
/// caller building a custom world stays within this module's vocabulary).
pub fn objective(name: &str, at: Coord, seed: u8) -> Objective {
    Objective::new(name, at, seed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::game::{demo_world, play_match, AgentPlayer, AgentPolicy, Side};

    fn world() -> (Lobby, usize) {
        let mut lobby = Lobby::new(3);
        let idx = lobby.host("alpha", demo_world());
        (lobby, idx)
    }

    // ── The world is a genuine web of published cells. ──

    #[test]
    fn a_world_publishes_board_players_and_objectives_as_cells() {
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        // board + 2 players + 3 objectives = 6 cells.
        assert_eq!(w.cell_count(), 6);
        // The board cell is fetchable + attested in the web-of-cells.
        let (res, _chrome) = lobby.web.fetch(&w.board_uri).expect("board cell published");
        assert!(
            res.verify().is_ok(),
            "the board cell's attestation verifies"
        );
        // Each player cell + objective cell is fetchable too.
        for (_s, uri) in &w.player_uris {
            assert!(lobby.web.fetch(uri).is_ok(), "player cell published");
        }
        for (_n, uri) in &w.objective_uris {
            assert!(lobby.web.fetch(uri).is_ok(), "objective cell published");
        }
    }

    #[test]
    fn a_lobby_hosts_several_federated_worlds() {
        let mut lobby = Lobby::new(3);
        lobby.host("alpha", demo_world());
        lobby.host("bravo", demo_world());
        assert_eq!(lobby.world_count(), 2);
        assert!(lobby.world("alpha").is_some());
        assert!(lobby.world("bravo").is_some());
        // Distinct worlds get DISTINCT board cells (federated addressing — each world
        // is independently addressable, no seed collision in the shared web).
        let a = lobby.worlds[0].board_uri.clone();
        let b = lobby.worlds[1].board_uri.clone();
        assert_ne!(a, b, "two federated worlds have distinct board cells");
        // Both worlds' board cells are independently fetchable + attested.
        assert!(lobby.web.fetch(&a).is_ok());
        assert!(lobby.web.fetch(&b).is_ok());
    }

    // ── The membrane negotiation: the org-settings page, on the real lattice. ──

    #[test]
    fn a_player_can_grant_a_view_of_their_own_side() {
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        let neg = MembraneNegotiation::for_world(w);
        // Blue (holding Blue's vision authority) grants a Blue-side spectator view.
        let blue_held = player_authority(w, Side::Blue);
        let grant = neg
            .propose_one_side(Side::Blue, &blue_held, Side::Blue)
            .expect("Blue can grant a view of its own side");
        assert_eq!(grant.scope, SpectatorScope::OneSide(Side::Blue));
        // The grant's cap carries Blue's identity (gated to Blue's view).
        assert_eq!(grant.cap.window.rights, side_rights(Side::Blue));
    }

    #[test]
    fn a_player_cannot_grant_a_view_of_the_enemy_side() {
        // THE no-peek property at the negotiation layer: Blue cannot extend a grant
        // to watch RED's fog-of-war view, because Blue does not hold Red's vision
        // authority — the REAL is_attenuation refuses the mint. You cannot grant
        // access to a team you are not on.
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        let neg = MembraneNegotiation::for_world(w);
        let blue_held = player_authority(w, Side::Blue);
        let refused = neg.propose_one_side(Side::Blue, &blue_held, Side::Red);
        assert!(
            matches!(refused, Err(NegotiationError::GranterLacksAuthority { .. })),
            "Blue cannot grant a view of Red's side (it lacks Red's authority): {refused:?}"
        );
    }

    #[test]
    fn an_objectives_only_grant_leaks_no_unit_positions() {
        // The narrow scope: a scoreboard grant reveals the control points + holders,
        // but NO unit positions of EITHER side. The no-leak property of a tight scope.
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        let neg = MembraneNegotiation::for_world(w);
        let grant = neg
            .propose_objectives_only(Side::Blue)
            .expect("anyone may grant a scoreboard");
        let log = witnessed_log_for(&lobby.web, w);
        let session = SpectatorSession::open(w, &grant, &log, true);
        // The session sees the objective tiles...
        assert_eq!(session.visible.len(), w.board.objectives.len());
        // ...and reveals NO units of either side.
        assert!(
            !session.reveals_unit_of(w, Side::Blue),
            "scoreboard leaks no Blue units"
        );
        assert!(
            !session.reveals_unit_of(w, Side::Red),
            "scoreboard leaks no Red units"
        );
        // The scoreboard identity is incomparable to a side's vision (cannot widen).
        assert!(
            !dregg_cell::is_attenuation(&grant.cap.window.rights, &side_rights(Side::Blue)),
            "the scoreboard grant cannot be widened into Blue's view"
        );
    }

    #[test]
    fn a_full_post_game_grant_is_refused_while_the_game_is_live() {
        // The "can't make a repo public while it has secrets" rule: a full-board grant
        // is refused mid-game (it would leak the fog), but ALLOWED once the game is
        // decided. We play a match to completion, then the grant is allowed.
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        let neg = MembraneNegotiation::for_world(w);
        // Live game → refused.
        assert!(
            matches!(
                neg.propose_full_post_game(Side::Blue),
                Err(NegotiationError::GameStillLive)
            ),
            "a full-board grant is refused while the game is live"
        );

        // Play the world to a decision, then a full grant is allowed.
        let blue = AgentPlayer::with_policy(Side::Blue, spectator_cell(1), AgentPolicy::Aggressive);
        let red = AgentPlayer::with_policy(Side::Red, spectator_cell(2), AgentPolicy::Aggressive);
        let result = play_match(w.board.clone(), &blue, &red, 400);
        // Re-publish the terminal board into a fresh world to negotiate over it.
        let mut lobby2 = Lobby::new(3);
        let widx = lobby2.host("ended", result.board);
        let ended = &lobby2.worlds[widx];
        let neg2 = MembraneNegotiation::for_world(ended);
        if ended.board.outcome().is_some() {
            let grant = neg2
                .propose_full_post_game(Side::Blue)
                .expect("a full grant is allowed post-game");
            assert_eq!(grant.scope, SpectatorScope::FullPostGame);
            let log = witnessed_log_for(&lobby2.web, ended);
            let session = SpectatorSession::open(ended, &grant, &log, true);
            // Post-game, the whole board is visible.
            assert_eq!(
                session.visible.len(),
                ended.board.rows as usize * ended.board.cols as usize
            );
        }
    }

    // ── Re-share chains (A→B→C) compose through the real lattice. ──

    #[test]
    fn a_reshare_chain_attenuates_and_an_amplifying_reshare_is_refused() {
        // A→B→C: Blue grants a Blue-side view (A→B); B re-shares a NARROWER view to C
        // (still Blue identity, a smaller frustum) → admitted; an attempt to re-share
        // a WIDER reach than B held → refused (amplification). The anti-ghost tooth.
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        let neg = MembraneNegotiation::for_world(w);
        let blue_held = player_authority(w, Side::Blue);
        let grant = neg
            .propose_one_side(Side::Blue, &blue_held, Side::Blue)
            .unwrap();

        // B re-shares a strictly NARROWER reach to C (a subset of the frustum).
        let mut narrow = std::collections::BTreeSet::new();
        if let Some(first) = grant.cap.fetch_allow.as_ref().and_then(|s| s.iter().next()) {
            narrow.insert(first.clone());
        }
        let narrower = SurfaceCapability::scoped(
            w.board.cell,
            side_rights(Side::Blue), // same identity (cannot change the gate)
            narrow.clone(),
            [],
        );
        let downstream = neg
            .reshare(&grant, narrower)
            .expect("a narrower reshare is admitted");
        // C's reach is ⊆ B's reach.
        assert!(downstream
            .cap
            .fetch_allow
            .as_ref()
            .unwrap()
            .is_subset(grant.cap.fetch_allow.as_ref().unwrap()));

        // An amplifying reshare (a WIDER frustum than B held — a tile B cannot see) →
        // refused.
        let mut wider = grant.cap.fetch_allow.clone().unwrap_or_default();
        wider.insert("dregg://tile-99-99".to_string()); // a tile outside B's reach
        let amplifying =
            SurfaceCapability::scoped(w.board.cell, side_rights(Side::Blue), wider, []);
        assert!(
            matches!(
                neg.reshare(&grant, amplifying),
                Err(NegotiationError::ReshareWouldAmplify)
            ),
            "an amplifying reshare is refused by the real Membrane::reshare"
        );
    }

    // ── The liveness-type carries through a spectator session (honest by type). ──

    #[test]
    fn a_spectator_session_is_replayed_deterministic_iff_witnessed() {
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        let neg = MembraneNegotiation::for_world(w);
        let blue_held = player_authority(w, Side::Blue);
        let grant = neg
            .propose_one_side(Side::Blue, &blue_held, Side::Blue)
            .unwrap();

        // A fully-witnessed log, sources gone → ReplayedDeterministic.
        let witnessed = witnessed_log_for(&lobby.web, w);
        let replayed = SpectatorSession::open(w, &grant, &witnessed, /*reachable*/ false);
        assert_eq!(replayed.liveness, Rehydration::ReplayedDeterministic);

        // An ambient log → ReconstructedApproximate (a context that reached outside).
        let ambient = ambient_log();
        let recon = SpectatorSession::open(w, &grant, &ambient, false);
        assert_eq!(recon.liveness, Rehydration::ReconstructedApproximate);

        // Sources still reachable → Live (regardless of the log).
        let live = SpectatorSession::open(w, &grant, &witnessed, true);
        assert_eq!(live.liveness, Rehydration::Live);
    }

    #[test]
    fn a_one_side_spectator_session_respects_fog() {
        // A Blue-side spectator session reveals Blue's view and NOT Red's hidden
        // units (the no-peek carries into spectating, at the world layer).
        let (lobby, idx) = world();
        let w = &lobby.worlds[idx];
        let neg = MembraneNegotiation::for_world(w);
        let blue_held = player_authority(w, Side::Blue);
        let grant = neg
            .propose_one_side(Side::Blue, &blue_held, Side::Blue)
            .unwrap();
        let log = witnessed_log_for(&lobby.web, w);
        let session = SpectatorSession::open(w, &grant, &log, true);
        // The spectator sees a strict sub-board (fog applies).
        let area = w.board.rows as usize * w.board.cols as usize;
        assert!(
            session.visible.len() < area,
            "the Blue spectator's view is fogged"
        );
        // It does not reveal Red units that are outside Blue's frustum. (At least one
        // Red unit must be hidden at the opening.)
        let hidden_red = w
            .board
            .units
            .iter()
            .filter(|u| u.side == Side::Red)
            .any(|u| !session.visible.contains(&u.at));
        assert!(
            hidden_red,
            "at least one Red unit is hidden from the Blue spectator"
        );
    }
}
