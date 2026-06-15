//! `DeosApp` — **the deos-app composition**: the six layers wired into ONE shape.
//!
//! `docs/deos/DEOS-APPS.md` (§"the deos app model"): a **deos app** is a set of
//! **cells** exposing **affordances** (cap-gated verified-turn templates) → rendered
//! as **web surfaces** → over **durable verified state** → reached by **agents**
//! (human or AI) through the **SDKs** → distributed across the **web-of-cells**
//! (federated, sturdyref-linked) → **rehydratable** (frustum-snapshots). The gap the
//! doc names (§6): "the pg-dregg / sdk / web-surface stack is uncomposed … three good
//! pieces that *do not yet compose* into the deos app stack." `DeosApp` IS that
//! composition.
//!
//! The framework already had the bones SEPARATELY — [`AffordanceSurface`] + the
//! [`crate::affordance_endpoint`] HTTP surface, the [`StarbridgeAppContext`]
//! registration, the [`AppCipherclerk`] + [`EmbeddedExecutor`] SDK surface, the
//! [`CapTpServer`] + [`NameserviceClient`] web-of-cells distribution, and the
//! [`crate::rehydration`] frustum-snapshots. `DeosApp` composes them into **ONE
//! registration** so an app builder writes *affordances + a surface* and the
//! framework wires the verified state, the SDK surface, the distribution, and the
//! rehydration — `register(ctx)` becomes `DeosApp::builder(...).cell(...).build()`,
//! and ONE `mount()` yields the whole axum surface.
//!
//! ## The shape
//!
//! ```ignore
//! let app = DeosApp::builder("doc-app", cipherclerk, executor)
//!     .federation(FederationId([0xAB; 32]))
//!     // one cell exposing its affordances; published into the web-of-cells:
//!     .cell(DeosCell::new(doc, "doc")
//!         .affordance(CellAffordance::new("view",  AuthRequired::Signature, view_fx))
//!         .affordance(CellAffordance::new("edit",  AuthRequired::Either,    edit_fx))
//!         .affordance(CellAffordance::new("admin", AuthRequired::None,      admin_fx))
//!         .publish(AuthRequired::Signature)) // exported as a sturdyref at this authority
//!     .discoverable(vec!["docs".into()])     // auto-registers in the nameservice
//!     .build();
//!
//! // ONE registration onto the shared host context (alongside other deos apps):
//! app.register(&ctx);
//!
//! // ONE mount yields the whole HTTP surface (per-cell affordance routers + the
//! // app manifest + the web-of-cells snapshot endpoints):
//! let router = app.mount();
//! ```
//!
//! ## What each layer becomes
//!
//! - **cells × affordances** → [`DeosCell`] bundles a backing cell with its
//!   [`AffordanceSurface`]; [`DeosApp`] holds many.
//! - **the SDK surface** → the app carries the [`AppCipherclerk`] + [`EmbeddedExecutor`]
//!   every fire routes through (the verified-turn dispatch seam, already closed).
//! - **web-of-cells distribution** → a published cell is exported through the
//!   [`CapTpServer`] as a `dregg://` sturdyref ([`DeosApp::publish_all`]) AND
//!   registered in the nameservice ([`DeosApp::announce`]).
//! - **rehydratable** → [`DeosCell::snapshot`] mints a [`crate::rehydration::Sturdyref`]
//!   a peer rehydrates per-viewer through a [`crate::rehydration::Membrane`] — the
//!   frustum-snapshot, composed with the cell's live affordance surface.
//! - **durable verified state** → a DOCUMENTED SEAM ([`PersistenceSeam`]): the
//!   pg-dregg layer (reads are free SQL, writes are verified turns) plugs in here.
//!   Marked honestly, NOT faked — the embedded executor is the in-process state today.

use std::sync::Arc;

use axum::{Json, Router, routing::get};
use dregg_cell::{AuthRequired, CellProgram, StateConstraint};
use dregg_types::{CellId, FederationId};
use serde_json::json;

use crate::affordance::{
    AffordanceSurface, CellAffordance, FireError, FireExecuteError, GatedAffordance, GatedSurface,
};
use crate::affordance_endpoint::{AffordanceEndpoint, HeldRightsResolver};
use crate::captp_server::CapTpServer;
use crate::cipherclerk::{AppCipherclerk, EmbeddedExecutor};
use crate::discovery::{NameRegistration, NameserviceClient};
use crate::rehydration::{InteractionLog, Membrane, RehydrateError, RehydratedSurface, Sturdyref};
use crate::starbridge::StarbridgeAppContext;

// =============================================================================
// DeosCell — one cell exposing affordances, optionally published
// =============================================================================

/// One **cell exposing affordances** within a deos app — a backing cell, its
/// [`AffordanceSurface`], and (optionally) the authority at which it is published
/// into the web-of-cells.
///
/// This is the atom of the deos app model: "a set of cells exposing affordances."
/// An app holds many; each renders to its own HTTP affordance router and (if
/// published) its own `dregg://` sturdyref + rehydratable snapshot.
#[derive(Clone, Debug)]
pub struct DeosCell {
    surface: AffordanceSurface,
    /// The cell's **gated** affordances — those carrying BOTH a cap-gate AND a
    /// live-state gate (the htmx-on-crack conjunction; the Rust twin of the Lean
    /// `Dregg2.Deos.GatedAffordance`). A gated affordance's button lights for a
    /// viewer IFF the viewer holds the cap AND the cell's LIVE state admits the
    /// fire. The framework reads the live state (via the [`EmbeddedExecutor`]) so the
    /// author never hand-threads `(old, new)` at the boundary — the surface REACTS to
    /// the cell. Kept alongside `surface` (the cap-only affordances) so a cell can
    /// expose both kinds; the gated set is the state-aware part.
    gated: GatedSurface,
    /// If `Some(authority)`, this cell is EXPORTED into the web-of-cells at
    /// `authority` (a sturdyref bearer obtains `authority` on enliven). `None` ⇒
    /// local-only (reachable through the app's own HTTP surface but not published as
    /// a cross-cell sturdyref).
    published_at: Option<AuthRequired>,
    /// The route prefix this cell's affordance router mounts at. Defaults to
    /// `/{surface_name}` (or `/cell-{hex8}` if unnamed).
    route_prefix: String,
}

impl DeosCell {
    /// A cell `cell` exposing a named affordance surface. Add affordances with
    /// [`DeosCell::affordance`].
    pub fn new(cell: CellId, name: impl Into<String>) -> Self {
        let name = name.into();
        let route_prefix = if name.is_empty() {
            format!("/cell-{}", hex8(&cell))
        } else {
            format!("/{name}")
        };
        DeosCell {
            surface: AffordanceSurface::named(cell, name.clone()),
            gated: GatedSurface::named(cell, name),
            published_at: None,
            route_prefix,
        }
    }

    /// Declare (or replace, by name) an affordance on this cell. Builder-style.
    pub fn affordance(mut self, affordance: CellAffordance) -> Self {
        self.surface = self.surface.declare(affordance);
        self
    }

    /// Declare (or replace, by name) a **gated affordance** on this cell — a
    /// cap-gated effect-template PLUS a live-state condition (the cap∧state
    /// conjunction). Builder-style.
    ///
    /// `docs/deos/DEOS.md` §"htmx on crack" + the Lean rung `Dregg2.Deos.GatedAffordance`:
    /// the button fires IFF the viewer HOLDS the cap AND the cell's LIVE state admits
    /// the fire. The framework reads the live state from the executor (see
    /// [`DeosCell::project_gated_for`] / [`DeosCell::fire_gated_through_executor`]) — so
    /// the surface is REACTIVE (a button dark in one state lights in another) without
    /// the author threading `(old, new)` by hand.
    ///
    /// ```ignore
    /// DeosCell::new(proposal, "proposal")
    ///     .gated(GatedAffordance::new(
    ///         CellAffordance::new("approve", AuthRequired::Either, approve_effect),
    ///         CellProgram::Predicate(vec![StateConstraint::FieldEquals { index: 0, value: pending }]),
    ///     ))
    /// ```
    pub fn gated(mut self, ga: GatedAffordance) -> Self {
        self.gated = self.gated.declare(ga);
        self
    }

    /// **Publish** this cell into the web-of-cells: export it as a `dregg://`
    /// sturdyref at `authority` (a bearer obtains `authority` on enliven) AND make it
    /// rehydratable at that lineage. Without this, the cell is local-only.
    pub fn publish(mut self, authority: AuthRequired) -> Self {
        self.published_at = Some(authority);
        self
    }

    /// Override the HTTP route prefix this cell's affordance router mounts at
    /// (default `/{name}`).
    pub fn at_route(mut self, prefix: impl Into<String>) -> Self {
        self.route_prefix = prefix.into();
        self
    }

    /// The backing cell.
    pub fn cell(&self) -> CellId {
        self.surface.cell
    }

    /// The route prefix this cell's affordance router mounts at.
    pub fn route_prefix(&self) -> &str {
        &self.route_prefix
    }

    /// The cell's affordance surface (read-only).
    pub fn surface(&self) -> &AffordanceSurface {
        &self.surface
    }

    /// The cell's **gated** affordance surface (read-only) — the cap∧state,
    /// state-aware affordances.
    pub fn gated_surface(&self) -> &GatedSurface {
        &self.gated
    }

    /// Whether this cell exposes any gated (cap∧state) affordances.
    pub fn has_gated(&self) -> bool {
        !self.gated.affordances.is_empty()
    }

    /// Is this cell published into the web-of-cells? If so, at what authority?
    pub fn published_authority(&self) -> Option<&AuthRequired> {
        self.published_at.as_ref()
    }

    /// Mint a **frustum-snapshot** [`Sturdyref`] of this cell at its published
    /// lineage (or `AuthRequired::None`/root if local-only), carrying `witness_log`
    /// and `sources_reachable`. A peer rehydrates it per-viewer through a
    /// [`Membrane`] (see [`DeosCell::rehydrate`]).
    ///
    /// The snapshot is TINY (the lineage + the witness-log + the culling boundary) —
    /// the affordance data is re-expanded from the live surface at rehydration.
    pub fn snapshot(&self, witness_log: InteractionLog, sources_reachable: bool) -> Sturdyref {
        let lineage = self.published_at.clone().unwrap_or(AuthRequired::None);
        Sturdyref::new(self.cell(), lineage, witness_log, sources_reachable)
    }

    /// **Rehydrate** a snapshot of this cell for a viewer holding `viewer_held`,
    /// through the membrane, against THIS cell's live surface — the per-viewer
    /// affordance slice the viewer's `(held) ∧ (lineage)` meet authorizes (or
    /// [`RehydrateError::Amplification`] if incomparable). The deos-only novelty,
    /// composed with the cell's affordances.
    pub fn rehydrate(
        &self,
        snapshot: &Sturdyref,
        viewer_held: AuthRequired,
    ) -> Result<RehydratedSurface, RehydrateError> {
        let membrane = Membrane::new(viewer_held);
        snapshot.rehydrate_for(&membrane, &self.surface)
    }

    /// **Predict** an optimistic fire on this cell (the interactive tempo) — the cap
    /// gate runs NOW, the local apply is provisional, and the verified turn settles at
    /// the boundary via [`crate::optimistic_fire::OptimisticFire::settle`].
    ///
    /// `DEOS-APPS.md` (§the interactive/real-time tempo gap): optimistic-local +
    /// verified-at-boundary (the #169 dial), wired onto this cell's affordances. The
    /// gate is the SAME real [`is_attenuation`] — optimism never weakens it (an
    /// unauthorized fire is refused at predict). Apply the predicted effect to a local
    /// view this frame; settle when you reach the trust boundary.
    pub fn predict_fire(
        &self,
        name: &str,
        actor: CellId,
        held: &AuthRequired,
    ) -> Result<crate::optimistic_fire::OptimisticFire, crate::affordance::FireError> {
        crate::optimistic_fire::OptimisticFire::predict(&self.surface, name, actor, held)
    }

    /// **The per-viewer, per-STATE gated-affordance projection** — the htmx-on-crack
    /// reactive button-set. Reads this cell's LIVE state from `executor` and returns
    /// the gated affordances a holder of `held` may fire AGAINST IT (those whose
    /// cap-gate AND state-gate both pass). The framework supplies the live state, so
    /// the surface REACTS to the cell:
    ///
    /// - two viewers DIVERGE by their caps (progressive attenuation, as before);
    /// - the SAME viewer's set CHANGES as the backing cell transitions (the htmx
    ///   tooth — a button enters/leaves the set on a state change).
    ///
    /// If the cell is not in the embedded ledger (no live state to gate on), the
    /// gated set is empty (fail-closed: no state ⇒ no state-gated fire). The Rust twin
    /// of Lean `projectGatedFor` / `projectGatedFor_state_reactive`.
    pub fn project_gated_for(
        &self,
        held: &AuthRequired,
        executor: &EmbeddedExecutor,
    ) -> Vec<GatedAffordance> {
        let Some(state) = executor.cell_state(self.cell()) else {
            return Vec::new();
        };
        // The state gate reads the post-transition `(old, new)`; for a projection
        // (no pending write yet) we gate on the cell's CURRENT state as both — "may
        // this button fire right now, in the state the cell is in".
        self.gated.project_gated_for(held, &state, &state)
    }

    /// The gated affordance names a viewer may fire against the cell's LIVE state
    /// (sorted) — the per-viewer, per-state button-set the same viewer DIVERGES on
    /// across states.
    pub fn gated_fireable_names(
        &self,
        held: &AuthRequired,
        executor: &EmbeddedExecutor,
    ) -> Vec<String> {
        let Some(state) = executor.cell_state(self.cell()) else {
            return Vec::new();
        };
        self.gated.fireable_names(held, &state, &state)
    }

    /// **Fire a gated affordance** as a viewer holding `held` — the cap∧state gate
    /// against the cell's LIVE state, then the closed dispatch seam through the
    /// `executor`. The framework reads the live state (so the author does not thread
    /// `(old, new)`), runs BOTH teeth IN-BAND, and on both passing submits the real
    /// verified turn, returning the executor's OWN [`dregg_turn::TurnReceipt`]:
    ///
    /// - the CAP tooth: an unheld fire is [`FireExecuteError::Gate`] /
    ///   [`FireError::Unauthorized`] (anti-ghost — nothing submitted);
    /// - the STATE tooth: a stale-state fire is [`FireExecuteError::Gate`] /
    ///   [`FireError::StateConditionUnmet`] (anti-ghost for the state tooth too —
    ///   nothing submitted, EVEN for a fully-authorized actor);
    /// - a missing gated affordance is [`FireError::NoSuchAffordance`];
    /// - a cell with no live state in the ledger is [`FireError::StateConditionUnmet`]
    ///   (fail-closed).
    ///
    /// The Rust twin of Lean `fireGated` carried through the executor.
    pub fn fire_gated_through_executor(
        &self,
        name: &str,
        held: &AuthRequired,
        cipherclerk: &AppCipherclerk,
        executor: &EmbeddedExecutor,
    ) -> Result<dregg_turn::TurnReceipt, FireExecuteError> {
        let ga = self
            .gated
            .get(name)
            .ok_or(FireExecuteError::Gate(FireError::NoSuchAffordance))?;
        let state = executor.cell_state(self.cell()).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: name.to_string(),
                reason: "cell has no live state in the embedded ledger (fail-closed)".to_string(),
            })
        })?;
        // The fire transitions FROM the current state; the gate evaluates the effect's
        // `(old, new)`. We gate on the live state as `old` and the affordance's own
        // produced state as `new` — but the GatedAffordance evaluates its `state_cond`
        // (a precondition predicate) against the touched cell's `(old, new)`; for a
        // precondition the relevant read is the current state, so we pass it as both
        // and let the executor re-enforce the program on the actual produced state.
        ga.fire_through_executor(held, &state, &state, cipherclerk, executor)
    }

    /// **Fire a STATE-PARAMETERIZED gated affordance** through the executor — the cap∧state
    /// gate, then a turn whose effects are DERIVED FROM THE CELL'S LIVE STATE by `effects`.
    ///
    /// The plain [`DeosCell::fire_gated_through_executor`] submits the affordance's CONSTANT
    /// effect template (so an accumulating button — a counter, a budget meter — can only fire
    /// once). This drives the SAME published cap∧state button across a MULTI-STEP run: the
    /// effects are a pure function of the cell's current [`dregg_cell::state::CellState`], so an
    /// accumulating fire (`spent := live_spent + cost`, `epoch := live_epoch + 1`) advances each
    /// time. The gate is unchanged (cap∧state, anti-ghost); the executor re-enforces the cell
    /// program on the produced transition. Delegates to
    /// [`crate::affordance::GatedAffordance::fire_through_executor_with`].
    pub fn fire_gated_through_executor_with<F>(
        &self,
        name: &str,
        held: &AuthRequired,
        cipherclerk: &AppCipherclerk,
        executor: &EmbeddedExecutor,
        effects: F,
    ) -> Result<dregg_turn::TurnReceipt, FireExecuteError>
    where
        F: FnOnce(&dregg_cell::state::CellState) -> Vec<crate::Effect>,
    {
        let ga = self
            .gated
            .get(name)
            .ok_or(FireExecuteError::Gate(FireError::NoSuchAffordance))?;
        ga.fire_through_executor_with(held, cipherclerk, executor, effects)
    }
}

// =============================================================================
// PersistenceSeam — the documented pg-dregg seam (NOT faked)
// =============================================================================

/// The **durable-verified-state seam** — where pg-dregg plugs in.
///
/// `DEOS-APPS.md` (§"the deos app model"): durable verified state means "reads are
/// free SQL, writes are verified turns." That is the `pg-dregg` layer. This enum is
/// the HONEST marker of which backing a [`DeosApp`] uses — it does NOT fake the
/// durable layer (the framework must not add a hard pg-dregg dependency: pg-dregg is
/// a separate crate under active development). Today every deos app runs on
/// [`PersistenceSeam::EmbeddedLedger`] (the in-process verified ledger the
/// [`EmbeddedExecutor`] owns); [`PersistenceSeam::PgDregg`] is the named plug-in
/// point the host wires when the durable layer is available.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum PersistenceSeam {
    /// The in-process verified ledger the embedded executor owns (the state today).
    /// Reads + writes both go through the embedded executor; state is per-process.
    #[default]
    EmbeddedLedger,
    /// The durable pg-dregg layer (reads are free SQL, writes are verified turns) —
    /// the NAMED next layer. The framework keeps this a marker (no hard dependency);
    /// a host that has pg-dregg wired sets this so the app advertises durable state.
    PgDregg,
}

impl PersistenceSeam {
    /// A one-line description for the app manifest (so the durable-state posture is
    /// VISIBLE, never silently faked).
    pub fn describe(&self) -> &'static str {
        match self {
            PersistenceSeam::EmbeddedLedger => {
                "embedded-ledger (in-process verified state; reads + writes via the embedded executor)"
            }
            PersistenceSeam::PgDregg => {
                "pg-dregg (durable verified state: reads are free SQL, writes are verified turns)"
            }
        }
    }
}

// =============================================================================
// DeosApp + its builder
// =============================================================================

/// A **composed deos app** — the six layers wired into one shape (see module docs).
///
/// Holds the app's cells (each exposing affordances), the SDK surface (cipherclerk +
/// executor) every fire routes through, the web-of-cells distribution handles
/// (federation id, optional captp server + nameservice tags), the persistence-seam
/// marker, and an optional shared held-rights resolver for the affordance endpoints.
///
/// Construct through [`DeosApp::builder`]; [`DeosApp::register`] folds it into a
/// [`StarbridgeAppContext`] and [`DeosApp::mount`] yields the whole axum [`Router`].
#[derive(Clone)]
pub struct DeosApp {
    name: String,
    cipherclerk: AppCipherclerk,
    executor: EmbeddedExecutor,
    federation: FederationId,
    cells: Vec<DeosCell>,
    /// Optional captp server the published cells are exported through (the
    /// web-of-cells sturdyref minter). When absent, [`DeosApp::publish_all`] returns
    /// no URIs (publication is a no-op without a server).
    captp: Option<CapTpServer>,
    /// If `Some(tags)`, the app auto-registers in the nameservice on
    /// [`DeosApp::announce`] under `name` with these tags.
    discovery_tags: Option<Vec<String>>,
    /// The durable-state seam this app runs on (honest marker; pg-dregg plugs in).
    persistence: PersistenceSeam,
    /// Optional shared held-rights resolver for every cell's affordance endpoint
    /// (e.g. one backed by the verified presentation in production). Defaults to the
    /// header resolver.
    resolver: Option<Arc<dyn HeldRightsResolver>>,
}

impl DeosApp {
    /// Start building a deos app named `name`, driven by `cipherclerk` + `executor`
    /// (the SDK surface every verified-turn fire routes through).
    pub fn builder(
        name: impl Into<String>,
        cipherclerk: AppCipherclerk,
        executor: EmbeddedExecutor,
    ) -> DeosAppBuilder {
        let federation = FederationId(*cipherclerk.federation_id());
        DeosAppBuilder {
            app: DeosApp {
                name: name.into(),
                cipherclerk,
                executor,
                federation,
                cells: Vec::new(),
                captp: None,
                discovery_tags: None,
                persistence: PersistenceSeam::default(),
                resolver: None,
            },
        }
    }

    /// The app name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The app's cells.
    pub fn cells(&self) -> &[DeosCell] {
        &self.cells
    }

    /// Look up a cell by its backing CellId.
    pub fn cell(&self, cell: &CellId) -> Option<&DeosCell> {
        self.cells.iter().find(|c| c.cell() == *cell)
    }

    /// The SDK surface (signing handle).
    pub fn cipherclerk(&self) -> &AppCipherclerk {
        &self.cipherclerk
    }

    /// The SDK surface (turn-submission handle).
    pub fn executor(&self) -> &EmbeddedExecutor {
        &self.executor
    }

    /// The durable-state seam this app runs on (honest marker).
    pub fn persistence(&self) -> PersistenceSeam {
        self.persistence
    }

    /// **Register** this app onto a shared [`StarbridgeAppContext`] — the deos app
    /// model's composed `register(ctx)`. Every cell's affordance surface is folded
    /// into the context's [`crate::starbridge::AffordanceRegistry`], so a host
    /// mounting many deos apps serves them uniformly. Returns the registered cells'
    /// keys.
    ///
    /// This is the ONE registration the doc asks for: not factories+inspectors+
    /// affordances as separate verbs, but the app's whole cells×affordances surface
    /// in one fold.
    pub fn register(&self, ctx: &StarbridgeAppContext) -> Vec<[u8; 32]> {
        self.cells
            .iter()
            .map(|c| ctx.register_affordance_surface(c.surface.clone()))
            .collect()
    }

    /// **Mount** the whole app as an axum [`Router`] — the ONE mount the doc asks for.
    ///
    /// Yields:
    /// - `GET /manifest` — the app manifest (cells, affordances, persistence seam,
    ///   distribution posture) — the anti-drift descriptor a UI/agent reads to learn
    ///   the whole app surface;
    /// - per-cell, nested at the cell's route prefix: the [`AffordanceEndpoint`]
    ///   router (`/{cell}/descriptor`, `/{cell}/projected`, `/{cell}/fire/{name}`) —
    ///   the cap-gated per-viewer surface + the verified-turn fire.
    ///
    /// Every fire routes through the app's shared cipherclerk + executor (the closed
    /// dispatch seam). The held-rights resolver is the app's (default header).
    pub fn mount(&self) -> Router {
        let mut router = Router::new();
        // The app manifest — the whole surface, from the Rust source of truth.
        let manifest = self.manifest();
        router = router.route(
            "/manifest",
            get(move || {
                let manifest = manifest.clone();
                async move { Json(manifest) }
            }),
        );

        // The web surface — the `<dregg-affordance-surface>` web component (the
        // htmx-on-crack custom element the embedded servo web-surface mounts). Served
        // as a JS module from the Rust source of truth (anti-drift). DEOS.md: a deos
        // app is "rendered as web surfaces."
        let surface_js = crate::webgen::render_surface_component(self);
        router = router.route(
            "/surface.js",
            get(move || {
                let surface_js = surface_js.clone();
                async move {
                    (
                        [(
                            axum::http::header::CONTENT_TYPE,
                            "text/javascript; charset=utf-8",
                        )],
                        surface_js,
                    )
                }
            }),
        );

        for c in &self.cells {
            let mut endpoint = AffordanceEndpoint::new(
                c.surface.clone(),
                self.cipherclerk.clone(),
                self.executor.clone(),
            )
            // Thread the cell's GATED (cap∧state) surface so `/gated/projected` +
            // `/gated/fire/{name}` are served — the htmx-on-crack reactive button-set over HTTP.
            .with_gated(c.gated.clone());
            if let Some(resolver) = &self.resolver {
                endpoint = endpoint.with_resolver(Arc::clone(resolver));
            }
            router = router.nest(&c.route_prefix, endpoint.router(&c.route_prefix));
        }
        router
    }

    /// The app **manifest** — a JSON descriptor of the whole composed surface, from
    /// the Rust source of truth (the anti-drift readout a UI/agent fetches to learn
    /// the app without hand-copying anything).
    ///
    /// Names every cell, its route prefix, whether it is published into the
    /// web-of-cells (and at what authority), and each affordance's required rights +
    /// effect kind + fire endpoint. Also names the persistence seam + the federation,
    /// so the app's durable-state + distribution posture is VISIBLE.
    pub fn manifest(&self) -> serde_json::Value {
        let cells: Vec<serde_json::Value> = self
            .cells
            .iter()
            .map(|c| {
                let desc = c.surface.descriptor(&c.route_prefix);
                // The GATED affordances — each with its cap-gate AND its live-state
                // gate (the htmx-on-crack conjunction). The `stateGate` field names
                // the state condition (the REAL CellProgram), and the
                // `projectedEndpoint`/`fireEndpoint` are STATE-AWARE (the surface
                // reacts to the cell). DEOS.md §"htmx on crack".
                let prefix = c.route_prefix.trim_end_matches('/');
                let gated: Vec<serde_json::Value> = c
                    .gated
                    .affordances
                    .iter()
                    .map(|g| {
                        json!({
                            "name": g.name(),
                            "requiredRights": format!("{:?}", g.affordance.required_rights),
                            "effectKind": g.affordance.effect_summary().variant_tag(),
                            "stateGate": describe_state_gate(&g.state_cond),
                            "fireEndpoint": format!("{prefix}/gated/fire/{}", g.name()),
                        })
                    })
                    .collect();
                json!({
                    "cell": hex_full(&c.cell()),
                    "name": desc.surface,
                    "routePrefix": c.route_prefix,
                    "published": c.published_at.as_ref().map(|a| format!("{a:?}")),
                    "snapshotEndpoint": format!("{}/snapshot", c.route_prefix),
                    "affordances": desc.elements.iter().map(|e| json!({
                        "name": e.name,
                        "requiredRights": e.required_rights,
                        "effectKind": e.effect_kind,
                        "fireEndpoint": e.fire_endpoint,
                    })).collect::<Vec<_>>(),
                    // The state-aware (cap∧state) affordances, if any. Their projection
                    // (which buttons light) depends on the cell's LIVE state.
                    "gatedAffordances": gated,
                    "gatedProjectedEndpoint": format!("{prefix}/gated/projected"),
                })
            })
            .collect();
        json!({
            "app": self.name,
            "federation": hex_full_arr(&self.federation.0),
            "persistence": self.persistence.describe(),
            "discoverable": self.discovery_tags.clone(),
            "webOfCells": self.captp.is_some(),
            "cells": cells,
        })
    }

    /// **Publish** every published cell into the web-of-cells — export each through
    /// the [`CapTpServer`] as a `dregg://` sturdyref at its published authority, at
    /// `current_height`. Returns the minted URIs (one per published cell), as URI
    /// strings.
    ///
    /// A no-op (empty result) if no captp server was attached or no cell is
    /// published. This is the distribution layer: a published cell becomes a
    /// sturdyref agents reacquire across the membrane.
    pub async fn publish_all(&self, current_height: u64) -> Vec<String> {
        let Some(captp) = &self.captp else {
            return Vec::new();
        };
        let mut uris = Vec::new();
        for c in &self.cells {
            if let Some(authority) = &c.published_at {
                if let Some(uri) = captp
                    .export(c.cell(), authority.clone(), current_height, None)
                    .await
                {
                    uris.push(uri.to_uri_string());
                }
            }
        }
        uris
    }

    /// **Announce** the app in the nameservice (if [`DeosAppBuilder::discoverable`]
    /// was set) — register under the app name with its tags at `target_uri`.
    /// Best-effort; a failure is returned for the caller to log non-fatally.
    pub async fn announce(
        &self,
        target_uri: impl Into<String>,
    ) -> Result<(), crate::discovery::DiscoveryError> {
        let Some(tags) = &self.discovery_tags else {
            return Ok(());
        };
        let client = NameserviceClient::from_env();
        client
            .register(&NameRegistration {
                name: self.name.clone(),
                tags: tags.clone(),
                target_uri: target_uri.into(),
            })
            .await
    }
}

/// A concise human description of a gated affordance's **live-state gate** (the REAL
/// [`dregg_cell::CellProgram`]) — for the app manifest's `stateGate` field, so the
/// state half of the cap∧state conjunction is VISIBLE (which transition the cell must
/// admit for the button to light), never an opaque blob. This describes; it does NOT
/// evaluate — the evaluation is the EXISTING [`dregg_cell::CellProgram::evaluate`]
/// (`GatedAffordance::state_admits`).
fn describe_state_gate(program: &CellProgram) -> String {
    match program {
        // `CellProgram::None` admits every state — a gated affordance with no state
        // condition degrades to a plain cap-gate (the button's verdict is caps-only).
        CellProgram::None => "always (no live-state condition — caps-only)".to_string(),
        CellProgram::Predicate(constraints) => {
            if constraints.is_empty() {
                "always (empty predicate)".to_string()
            } else {
                let parts: Vec<String> = constraints.iter().map(describe_constraint).collect();
                parts.join(" AND ")
            }
        }
        CellProgram::Cases(cases) => {
            if cases.is_empty() {
                "never (no transition case matches — default-deny)".to_string()
            } else {
                format!("one of {} operation-scoped case(s)", cases.len())
            }
        }
        CellProgram::Circuit { .. } => "a circuit-proven transition".to_string(),
    }
}

/// A one-line description of a single [`dregg_cell::StateConstraint`] (the slot-caveat
/// atoms most apps use for an affordance's state gate). Falls back to the variant's
/// debug form for the less-common atoms — the point is the manifest names the gate's
/// SHAPE, not that it re-implements the evaluator.
fn describe_constraint(c: &StateConstraint) -> String {
    match c {
        StateConstraint::FieldEquals { index, value } => {
            format!("slot[{index}] == {}", field_tail_u64(value))
        }
        StateConstraint::FieldGte { index, value } => {
            format!("slot[{index}] >= {}", field_tail_u64(value))
        }
        StateConstraint::FieldLte { index, value } => {
            format!("slot[{index}] <= {}", field_tail_u64(value))
        }
        StateConstraint::Monotonic { index } => format!("slot[{index}] non-decreasing"),
        StateConstraint::StrictMonotonic { index } => format!("slot[{index}] strictly increasing"),
        StateConstraint::Immutable { index } => format!("slot[{index}] immutable"),
        StateConstraint::WriteOnce { index } => format!("slot[{index}] write-once"),
        other => format!("{other:?}"),
    }
}

/// Read a [`dregg_cell::FieldElement`] as the big-endian u64 in its last 8 bytes (the
/// comparison the field's `FieldEquals`/`FieldGte` atoms use), for display.
fn field_tail_u64(fe: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[24..32]);
    u64::from_be_bytes(b)
}

impl std::fmt::Debug for DeosApp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeosApp")
            .field("name", &self.name)
            .field("cells", &self.cells.len())
            .field("federation", &hex8_arr(&self.federation.0))
            .field("web_of_cells", &self.captp.is_some())
            .field("discoverable", &self.discovery_tags.is_some())
            .field("persistence", &self.persistence)
            .finish()
    }
}

/// Builder for a [`DeosApp`] (see [`DeosApp::builder`]).
pub struct DeosAppBuilder {
    app: DeosApp,
}

impl DeosAppBuilder {
    /// Add a [`DeosCell`] (a cell exposing affordances) to the app.
    pub fn cell(mut self, cell: DeosCell) -> Self {
        self.app.cells.push(cell);
        self
    }

    /// Set the federation this app operates in (defaults to the cipherclerk's
    /// federation id). The federation is named in the manifest + used for sturdyref
    /// export.
    pub fn federation(mut self, federation: FederationId) -> Self {
        self.app.federation = federation;
        self
    }

    /// Attach the [`CapTpServer`] published cells are exported through (the
    /// web-of-cells sturdyref minter). If a federation was not set explicitly, the
    /// server's federation is used.
    pub fn web_of_cells(mut self, captp: CapTpServer) -> Self {
        self.app.federation = captp.federation_id();
        self.app.captp = Some(captp);
        self
    }

    /// Make the app **discoverable** — auto-register in the nameservice on
    /// [`DeosApp::announce`] under the app name with `tags`.
    pub fn discoverable(mut self, tags: Vec<String>) -> Self {
        self.app.discovery_tags = Some(tags);
        self
    }

    /// Declare the durable-state seam this app runs on (honest marker; defaults to
    /// [`PersistenceSeam::EmbeddedLedger`]). A host that has pg-dregg wired sets
    /// [`PersistenceSeam::PgDregg`] so the app advertises durable state — the
    /// framework adds NO hard pg-dregg dependency.
    pub fn persistence(mut self, seam: PersistenceSeam) -> Self {
        self.app.persistence = seam;
        self
    }

    /// Set a shared held-rights resolver for every cell's affordance endpoint (e.g.
    /// one backed by the verified presentation). The gate applied to the resolved
    /// value is unchanged (the REAL `is_attenuation`).
    pub fn held_rights_resolver(mut self, resolver: Arc<dyn HeldRightsResolver>) -> Self {
        self.app.resolver = Some(resolver);
        self
    }

    /// Finish building the [`DeosApp`].
    pub fn build(self) -> DeosApp {
        self.app
    }
}

// =============================================================================
// hex helpers
// =============================================================================

fn hex_full(cell: &CellId) -> String {
    hex_full_arr(cell.as_bytes())
}

fn hex_full_arr(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn hex8(cell: &CellId) -> String {
    hex8_arr(cell.as_bytes())
}

fn hex8_arr(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for b in bytes.iter().take(8) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::action::{Effect, Event};

    fn emit_event(cell: CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: Event {
                topic: [1u8; 32],
                data: vec![],
            },
        }
    }

    fn set_field(cell: CellId, index: usize) -> Effect {
        Effect::SetField {
            cell,
            index,
            value: [7u8; 32],
        }
    }

    fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0xAB; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        (cclerk, executor)
    }

    /// The canonical composed doc-app: ONE cell (the agent's own) with three
    /// cap-gated affordances, published into the web-of-cells, discoverable.
    fn doc_app(cclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
        let doc = cclerk.cell_id();
        DeosApp::builder("doc-app", cclerk.clone(), executor.clone())
            .cell(
                DeosCell::new(doc, "doc")
                    .affordance(CellAffordance::new(
                        "view",
                        AuthRequired::Signature,
                        emit_event(doc),
                    ))
                    .affordance(CellAffordance::new(
                        "edit",
                        AuthRequired::Either,
                        set_field(doc, 1),
                    ))
                    .affordance(CellAffordance::new(
                        "admin",
                        AuthRequired::None,
                        emit_event(doc),
                    ))
                    .publish(AuthRequired::Signature),
            )
            .discoverable(vec!["docs".into()])
            .build()
    }

    #[test]
    fn the_app_composes_one_cell_with_its_affordances() {
        let (cclerk, executor) = agent();
        let app = doc_app(&cclerk, &executor);
        assert_eq!(app.name(), "doc-app");
        assert_eq!(app.cells().len(), 1);
        let cell = &app.cells()[0];
        assert_eq!(cell.route_prefix(), "/doc");
        assert_eq!(
            cell.surface().all_names(),
            vec!["admin".to_string(), "edit".to_string(), "view".to_string()]
        );
        assert_eq!(cell.published_authority(), Some(&AuthRequired::Signature));
    }

    #[test]
    fn one_registration_folds_every_cell_into_the_context() {
        // The composed register(ctx): the app's whole cells×affordances surface in
        // ONE fold — not factories+inspectors+affordances as separate verbs.
        let (cclerk, executor) = agent();
        let app = doc_app(&cclerk, &executor);
        let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

        let keys = app.register(&ctx);
        assert_eq!(keys.len(), 1);
        assert_eq!(keys[0], *cclerk.cell_id().as_bytes());
        assert_eq!(ctx.affordance_registry().len(), 1);
        let got = ctx.affordance_registry().get(&cclerk.cell_id()).unwrap();
        assert_eq!(got.all_names().len(), 3);
    }

    #[test]
    fn the_manifest_describes_the_whole_composed_surface() {
        let (cclerk, executor) = agent();
        let app = doc_app(&cclerk, &executor);
        let m = app.manifest();

        assert_eq!(m["app"], "doc-app");
        // The persistence seam is VISIBLE (honest, not faked) — embedded by default.
        assert!(
            m["persistence"]
                .as_str()
                .unwrap()
                .contains("embedded-ledger")
        );
        assert_eq!(m["discoverable"], json!(["docs"]));
        let cells = m["cells"].as_array().unwrap();
        assert_eq!(cells.len(), 1);
        let doc = &cells[0];
        assert_eq!(doc["name"], "doc");
        assert_eq!(doc["routePrefix"], "/doc");
        // Published into the web-of-cells at Signature.
        assert_eq!(doc["published"], "Signature");
        let affs = doc["affordances"].as_array().unwrap();
        assert_eq!(affs.len(), 3);
        let edit = affs.iter().find(|a| a["name"] == "edit").unwrap();
        assert_eq!(edit["requiredRights"], "Either");
        assert_eq!(edit["effectKind"], "SetField");
        assert_eq!(edit["fireEndpoint"], "/doc/fire/edit");
    }

    #[test]
    fn persistence_seam_is_honest_and_switchable() {
        let (cclerk, executor) = agent();
        // Default: embedded ledger (the state today).
        let app = doc_app(&cclerk, &executor);
        assert_eq!(app.persistence(), PersistenceSeam::EmbeddedLedger);
        // A host with pg-dregg wired advertises durable state — no hard dep added.
        let durable = DeosApp::builder("d", cclerk.clone(), executor.clone())
            .persistence(PersistenceSeam::PgDregg)
            .build();
        assert_eq!(durable.persistence(), PersistenceSeam::PgDregg);
        assert!(
            durable.manifest()["persistence"]
                .as_str()
                .unwrap()
                .contains("pg-dregg")
        );
    }

    #[test]
    fn a_published_cell_snapshots_and_rehydrates_per_viewer() {
        // The rehydration layer, composed: snapshot a published cell, a weaker viewer
        // rehydrates a NARROWER affordance set through the membrane.
        let (cclerk, executor) = agent();
        let app = doc_app(&cclerk, &executor);
        let cell = &app.cells()[0];

        // Snapshot at the published lineage (Signature). Sources still reachable ⇒ Live.
        let snap = cell.snapshot(InteractionLog::new(), true);
        assert_eq!(snap.lineage, AuthRequired::Signature);
        assert_eq!(snap.liveness(), crate::rehydration::Rehydration::Live);

        // A Signature viewer rehydrates {view} (the meet of Signature ∧ Signature) —
        // the published lineage gates what ANY viewer can reacquire.
        let view = cell.rehydrate(&snap, AuthRequired::Signature).unwrap();
        assert_eq!(view.visible_names(), vec!["view".to_string()]);

        // A viewer holding an INCOMPARABLE authority (a distinct Custom identity)
        // cannot rehydrate it at all — the membrane mints no projection.
        let blocked = cell.rehydrate(&snap, AuthRequired::Custom { vk_hash: [9u8; 32] });
        assert!(matches!(blocked, Err(RehydrateError::Amplification { .. })));
    }

    #[tokio::test]
    async fn publish_all_is_a_noop_without_a_captp_server() {
        // Honest: publication needs a web-of-cells server. Without one, publish_all
        // returns no URIs (the cell is local-only over HTTP).
        let (cclerk, executor) = agent();
        let app = doc_app(&cclerk, &executor);
        assert!(app.publish_all(100).await.is_empty());
        // The manifest reflects it: no web-of-cells.
        assert_eq!(app.manifest()["webOfCells"], false);
    }

    #[tokio::test]
    async fn publish_all_exports_published_cells_through_captp() {
        // With a captp server attached, every PUBLISHED cell is exported as a real
        // dregg:// sturdyref at its published authority.
        let (cclerk, executor) = agent();
        let doc = cclerk.cell_id();
        let captp = CapTpServer::new(FederationId([0xAB; 32]));
        let app = DeosApp::builder("doc-app", cclerk.clone(), executor.clone())
            .web_of_cells(captp)
            .cell(
                DeosCell::new(doc, "doc")
                    .affordance(CellAffordance::new(
                        "view",
                        AuthRequired::Signature,
                        emit_event(doc),
                    ))
                    .publish(AuthRequired::Signature),
            )
            .build();

        let uris = app.publish_all(100).await;
        assert_eq!(uris.len(), 1, "the one published cell is exported");
        assert!(
            uris[0].starts_with("dregg://"),
            "a real sturdyref URI: {}",
            uris[0]
        );
        // The manifest now advertises the web-of-cells.
        assert_eq!(app.manifest()["webOfCells"], true);
    }

    #[tokio::test]
    async fn the_mounted_router_serves_the_manifest_and_per_cell_fires() {
        use axum::body::Body;
        use axum::http::{Request, StatusCode};
        use tower::ServiceExt;

        let (cclerk, executor) = agent();
        let app = doc_app(&cclerk, &executor);
        let router = app.mount();

        // GET /manifest serves the whole composed surface.
        let m = router
            .clone()
            .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
            .await
            .unwrap();
        assert_eq!(m.status(), StatusCode::OK);

        // The per-cell affordance endpoint is mounted at /doc: an admin (root) fires
        // `admin` and the verified turn executes (the executor's own receipt).
        let fired = router
            .oneshot(
                Request::post("/doc/fire/admin")
                    .header(crate::affordance_endpoint::HELD_RIGHTS_HEADER, "root")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(
            fired.status(),
            StatusCode::OK,
            "the mounted fire executes a real turn"
        );
    }

    #[test]
    fn unpublished_cells_snapshot_at_root_lineage() {
        // A local-only (unpublished) cell still snapshots — at root lineage (None),
        // so its owner rehydrates the full surface but it is not in the web-of-cells.
        let (cclerk, executor) = agent();
        let doc = cclerk.cell_id();
        let app = DeosApp::builder("d", cclerk.clone(), executor.clone())
            .cell(DeosCell::new(doc, "doc").affordance(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                emit_event(doc),
            )))
            .build();
        let cell = &app.cells()[0];
        assert_eq!(cell.published_authority(), None);
        let snap = cell.snapshot(InteractionLog::new(), false);
        assert_eq!(
            snap.lineage,
            AuthRequired::None,
            "local-only ⇒ root lineage"
        );
    }
}
