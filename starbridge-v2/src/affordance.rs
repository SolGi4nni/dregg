//! Cell affordances — **htmx-on-crack, natively, with the seam CLOSED.**
//!
//! The deos interaction model (`docs/deos/DEOS.md`): a cell declares named, typed
//! **affordances** (effect-TEMPLATES); rendering one is a per-viewer projection
//! gated by held capabilities, and *firing* one is a **capability-gated verified
//! turn**. The `starbridge-web-surface` crate proved this thesis but had to leave
//! ONE seam named-not-closed — the firing → executed turn — because it has no
//! embedded executor (it models the dispatch the way `MockSurface` models the
//! libservo `WebView`'s dispatch).
//!
//! **Starbridge v2 closes that seam.** It EMBEDS the real verified executor
//! ([`crate::world::World`] over `dregg_turn::TurnExecutor`), so firing an
//! authorized affordance does not produce a *modeled* dispatch — it produces a
//! REAL `TurnReceipt` from the embedded executor. The whole loop runs in-process:
//!
//!   1. a cell publishes an [`AffordanceSurface`] — named effect-templates, each a
//!      real [`dregg_turn::Effect`] + the [`AuthRequired`] a viewer must HOLD;
//!   2. [`AffordanceSurface::project_for`] returns ONLY the affordances a viewer's
//!      held [`SurfaceCapability`] authorizes — progressive enhancement becomes
//!      progressive **attenuation**, gated by the GENUINE
//!      [`dregg_cell::is_attenuation`] (`required ⊆ held`), the same lattice the
//!      firmament + cap crown prove;
//!   3. [`AffordanceSurface::fire`] REFUSES an actor lacking the rights (the
//!      anti-ghost tooth) and otherwise mints an [`AffordanceIntent`] carrying the
//!      real effect;
//!   4. [`AffordanceIntent::fire_through_world`] hands that effect to
//!      [`World::commit_turn`] — the REAL executor — so the resulting
//!      [`TurnReceipt`] is the executor's own, chained on the agent's receipt
//!      chain. A turn that violates a guarantee (conservation, no-amplification,
//!      a permissions gate) is REJECTED by the executor, surfaced as
//!      [`FireOutcome::Refused`] — the verification axis firing in front of you.
//!
//! ## The firmament tie: a window IS a `Capability{ Surface(cell) }`
//!
//! The [`SurfaceCapability`] gating an affordance is the SAME real
//! `dregg_firmament` capability ([`crate::surface::SurfaceCapability`]) the
//! cap-first shell rides — `target = Surface(backing_cell)`, rights on the
//! `AuthRequired` lattice. So "who may press the button" is decided by the held
//! WINDOW capability, not a session cookie: an affordance-fire is a cap-gated
//! verified turn through the embedded executor, exactly the deos thesis, native.
//!
//! gpui-free and `cargo test`-able.

use dregg_cell::{is_attenuation, AuthRequired};
use dregg_turn::action::Effect;
use dregg_types::CellId;

use crate::surface::SurfaceCapability;
use crate::world::{CommitOutcome, World};

/// A single **cell affordance** — the htmx-on-crack element.
///
/// A `name` (the operation — the deos analogue of htmx's `hx-post` path), the
/// `required_rights` a viewer must HOLD over the surface's window cap to see/fire
/// it, and the `effect_template` it would fire — a real [`dregg_turn::Effect`],
/// the genuine turn the embedded executor runs.
///
/// `Effect` does not derive `PartialEq` (it carries proofs / eventual refs), so an
/// affordance is identified by `name` within a surface; the template is compared
/// structurally only where a test needs it, via [`AffordanceSurface::effect_summary`].
#[derive(Clone, Debug)]
pub struct CellAffordance {
    /// The operation name — unique within its [`AffordanceSurface`] (the deos
    /// analogue of `hx-post="/comment"`).
    pub name: String,
    /// The authority a viewer must HOLD over the surface's window cap to see/fire
    /// this affordance. The gate is `is_attenuation(held_rights, required)` =
    /// `required ⊆ held` — the viewer must hold AT LEAST this much authority. A
    /// `view` affordance requires a narrow right (any reader holds it); an `admin`
    /// affordance requires the broad root right (only a powerful holder clears it).
    pub required_rights: AuthRequired,
    /// The effect this affordance FIRES — a real [`dregg_turn::Effect`], the turn
    /// the embedded `TurnExecutor` runs. NOT a stub.
    pub effect_template: Effect,
}

impl CellAffordance {
    /// Declare an affordance named `name`, requiring `required_rights`, that fires
    /// `effect_template` (a real [`dregg_turn::Effect`]).
    pub fn new(
        name: impl Into<String>,
        required_rights: AuthRequired,
        effect_template: Effect,
    ) -> Self {
        CellAffordance {
            name: name.into(),
            required_rights,
            effect_template,
        }
    }

    /// Is this affordance authorized for a holder of the window cap `held`?
    ///
    /// THE cap-gate, the REAL one: `is_attenuation(held.rights, required)` =
    /// `required ⊆ held` (the proven attenuation lattice). True iff the holder's
    /// authority over the window is at least as broad as this affordance demands.
    /// The SAME predicate the shell runs to admit a window op and the cap crown
    /// proves — NOT a parallel role check.
    pub fn authorized_for(&self, held: &SurfaceCapability) -> bool {
        is_attenuation(held.rights(), &self.required_rights)
    }

    /// A stable, `Eq`-able summary of the effect-template (variant + touched
    /// cells), for diagnostics + tests (the `Effect` enum is not `PartialEq`).
    pub fn effect_summary(&self) -> EffectSummary {
        EffectSummary::of(&self.effect_template)
    }
}

/// A stable, comparable readout of a [`dregg_turn::Effect`] template — its variant
/// tag + the principal cell(s) it acts on. (The `Effect` enum is not `PartialEq`;
/// this is the equality-friendly projection a test or a view can compare.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectSummary {
    SetField { cell: CellId, index: usize },
    Transfer { from: CellId, to: CellId, amount: u64 },
    GrantCapability { from: CellId, to: CellId },
    RevokeCapability { cell: CellId, slot: u32 },
    EmitEvent { cell: CellId },
    IncrementNonce { cell: CellId },
    /// Any other real `Effect` variant, tagged by name (still the genuine effect —
    /// only the *summary* is coarse).
    Other { tag: &'static str },
}

impl EffectSummary {
    /// Summarize a real [`Effect`] for comparison/diagnostics.
    pub fn of(effect: &Effect) -> EffectSummary {
        match effect {
            Effect::SetField { cell, index, .. } => EffectSummary::SetField {
                cell: *cell,
                index: *index,
            },
            Effect::Transfer { from, to, amount } => EffectSummary::Transfer {
                from: *from,
                to: *to,
                amount: *amount,
            },
            Effect::GrantCapability { from, to, .. } => EffectSummary::GrantCapability {
                from: *from,
                to: *to,
            },
            Effect::RevokeCapability { cell, slot } => EffectSummary::RevokeCapability {
                cell: *cell,
                slot: *slot,
            },
            Effect::EmitEvent { cell, .. } => EffectSummary::EmitEvent { cell: *cell },
            Effect::IncrementNonce { cell } => EffectSummary::IncrementNonce { cell: *cell },
            other => EffectSummary::Other {
                tag: effect_variant_tag(other),
            },
        }
    }
}

/// The static variant tag of a real [`Effect`] (used by [`EffectSummary::Other`]).
fn effect_variant_tag(effect: &Effect) -> &'static str {
    match effect {
        Effect::SetField { .. } => "SetField",
        Effect::Transfer { .. } => "Transfer",
        Effect::GrantCapability { .. } => "GrantCapability",
        Effect::RevokeCapability { .. } => "RevokeCapability",
        Effect::EmitEvent { .. } => "EmitEvent",
        Effect::IncrementNonce { .. } => "IncrementNonce",
        Effect::CreateCell { .. } => "CreateCell",
        Effect::Burn { .. } => "Burn",
        Effect::CellSeal { .. } => "CellSeal",
        Effect::CellUnseal { .. } => "CellUnseal",
        Effect::CellDestroy { .. } => "CellDestroy",
        Effect::CreateCellFromFactory { .. } => "CreateCellFromFactory",
        Effect::MakeSovereign { .. } => "MakeSovereign",
        // A catch-all so a HARDSWAP that ADDS an `Effect` variant still compiles
        // here (the new variant summarizes as a fallback rather than breaking the
        // build). Any added variant is still the REAL effect.
        _ => "OtherEffect",
    }
}

/// A cell's published **affordance surface** — the set of affordances it exposes
/// (the deos analogue of a server's set of htmx endpoints).
///
/// Binds a `cell` (the surface's backing object) to its declared `affordances`.
/// Rendering it for a viewer is [`AffordanceSurface::project_for`] (CAP-GATED);
/// firing one is [`AffordanceSurface::fire`] (CAP-GATED, anti-ghost) →
/// [`AffordanceIntent::fire_through_world`] (the REAL embedded executor).
#[derive(Clone, Debug)]
pub struct AffordanceSurface {
    /// The cell backing this surface (the object whose affordances these are).
    pub cell: CellId,
    /// The declared affordances. Names are unique (a [`AffordanceSurface::declare`]
    /// with a duplicate name replaces the prior one).
    pub affordances: Vec<CellAffordance>,
}

/// Why an [`AffordanceSurface::fire`] was refused (the GATE, before the executor).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FireError {
    /// No affordance by that name on this surface.
    NoSuchAffordance,
    /// The actor's held window cap does NOT satisfy the affordance's
    /// `required_rights` — the anti-ghost tooth: a viewer firing an affordance they
    /// lack the rights for is REFUSED by the REAL `is_attenuation`, never run.
    Unauthorized {
        affordance: String,
        required: AuthRequired,
    },
}

impl AffordanceSurface {
    /// A surface over `cell` with no affordances yet.
    pub fn new(cell: CellId) -> Self {
        AffordanceSurface {
            cell,
            affordances: Vec::new(),
        }
    }

    /// Declare (or replace, by name) an affordance on this surface. Builder-style.
    pub fn declare(mut self, affordance: CellAffordance) -> Self {
        self.affordances.retain(|a| a.name != affordance.name);
        self.affordances.push(affordance);
        self
    }

    /// All declared affordance names (sorted), regardless of viewer.
    pub fn all_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.affordances.iter().map(|a| a.name.clone()).collect();
        names.sort();
        names
    }

    /// Look up an affordance by name.
    pub fn get(&self, name: &str) -> Option<&CellAffordance> {
        self.affordances.iter().find(|a| a.name == name)
    }

    /// **The per-viewer affordance projection.** Return ONLY the affordances a
    /// holder of the window cap `held` is authorized to see/fire — progressive
    /// enhancement becomes progressive **attenuation**.
    ///
    /// Each affordance is admitted iff [`CellAffordance::authorized_for`] — the REAL
    /// `is_attenuation` (`required ⊆ held`). Two viewers holding different window
    /// caps get DIFFERENT projections of the SAME surface. Declaration order is
    /// preserved (a stable sub-list).
    pub fn project_for(&self, held: &SurfaceCapability) -> Vec<CellAffordance> {
        self.affordances
            .iter()
            .filter(|a| a.authorized_for(held))
            .cloned()
            .collect()
    }

    /// The names a viewer is authorized to see (sorted) — the per-viewer affordance
    /// set, the thing two different-cap viewers DIVERGE on.
    pub fn visible_names(&self, held: &SurfaceCapability) -> Vec<String> {
        let mut names: Vec<String> = self
            .project_for(held)
            .into_iter()
            .map(|a| a.name)
            .collect();
        names.sort();
        names
    }

    /// A stable summary of one affordance's effect (for tests/diagnostics).
    pub fn effect_summary(&self, name: &str) -> Option<EffectSummary> {
        self.get(name).map(|a| a.effect_summary())
    }

    /// **Fire** the affordance named `name` as `actor`, holding window cap `held`.
    ///
    /// The htmx-on-crack interaction: pressing the "button" produces a verified-turn
    /// intent — the effect-template instantiated. The gate is in-band and REAL: the
    /// fire is admitted iff the actor's window cap satisfies the affordance's
    /// `required_rights` ([`CellAffordance::authorized_for`] = `is_attenuation`). The
    /// **anti-ghost tooth**: an actor firing an affordance they lack the rights for
    /// is [`FireError::Unauthorized`] — REFUSED, never run.
    ///
    /// On success returns an [`AffordanceIntent`] carrying the REAL
    /// [`dregg_turn::Effect`]. Hand it to [`AffordanceIntent::fire_through_world`] to
    /// execute the turn through the embedded executor.
    pub fn fire(
        &self,
        name: &str,
        actor: CellId,
        held: &SurfaceCapability,
    ) -> Result<AffordanceIntent, FireError> {
        let affordance = self.get(name).ok_or(FireError::NoSuchAffordance)?;
        if !affordance.authorized_for(held) {
            return Err(FireError::Unauthorized {
                affordance: name.to_string(),
                required: affordance.required_rights.clone(),
            });
        }
        Ok(AffordanceIntent {
            surface_cell: self.cell,
            affordance: affordance.name.clone(),
            actor,
            effect: affordance.effect_template.clone(),
        })
    }
}

/// The **verified-turn intent** firing an authorized affordance produces — the
/// effect-template instantiated, ready for the embedded executor.
///
/// It is ONLY ever minted by [`AffordanceSurface::fire`] AFTER the real
/// `is_attenuation` gate passed — so an intent's existence witnesses that the actor
/// was authorized. [`AffordanceIntent::fire_through_world`] closes the loop through
/// [`World::commit_turn`] (the SEAM the web crate could only name is CLOSED here,
/// because this process embeds the executor).
#[derive(Clone, Debug)]
pub struct AffordanceIntent {
    /// The cell whose affordance was fired (the surface's backing cell).
    pub surface_cell: CellId,
    /// The affordance name that was fired.
    pub affordance: String,
    /// The actor cell that fired it (the principal — the turn's `agent`).
    pub actor: CellId,
    /// The REAL effect the turn would run — the instantiated effect-template.
    pub effect: Effect,
}

/// The outcome of firing an affordance THROUGH the embedded executor — the seam,
/// closed. Either the executor committed the turn (a real [`TurnReceipt`]) or it
/// REJECTED it (a guarantee firing: conservation, no-amplification, a permissions
/// gate) — both are first-class, the rejection being the verification axis visible.
#[derive(Debug)]
pub enum FireOutcome {
    /// The embedded executor COMMITTED the affordance's turn. This receipt is the
    /// executor's own, chained on `actor`'s receipt chain.
    Committed(dregg_turn::turn::TurnReceipt),
    /// The embedded executor REJECTED the turn (a guarantee fired). The reason is
    /// the executor's own — surfaced, not hidden.
    Refused { reason: String, at_action: Vec<usize> },
}

impl FireOutcome {
    pub fn is_committed(&self) -> bool {
        matches!(self, FireOutcome::Committed(_))
    }
}

impl AffordanceIntent {
    /// The `Eq`-able summary of the effect this intent would run (the `Effect` is
    /// not `PartialEq`). Names the REAL effect.
    pub fn effect_summary(&self) -> EffectSummary {
        EffectSummary::of(&self.effect)
    }

    /// **Close the seam.** Execute this affordance's effect as a REAL verified turn
    /// through the embedded executor ([`World::commit_turn`]).
    ///
    /// The actor (`self.actor`) is the turn's `agent`; the single effect is the
    /// affordance's instantiated template. The executor threads the agent's
    /// receipt-chain head, runs the verified semantics, and EITHER commits (a real
    /// [`TurnReceipt`], [`FireOutcome::Committed`]) OR rejects (a guarantee fired —
    /// the actor lacked a permission, the turn broke conservation, a grant would
    /// amplify; [`FireOutcome::Refused`]). The gate that decided whether the
    /// affordance may fire AT ALL was the real `is_attenuation`
    /// ([`AffordanceSurface::fire`]); the gate that decides whether the resulting
    /// TURN commits is the real executor — both in-band, neither faked.
    ///
    /// This is what `starbridge-web-surface`'s `fire` could only MODEL (it has no
    /// embedded executor): here the receipt is the executor's, not a commitment.
    pub fn fire_through_world(&self, world: &mut World) -> FireOutcome {
        let turn = world.turn(self.actor, vec![self.effect.clone()]);
        match world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => FireOutcome::Committed(receipt),
            CommitOutcome::Rejected { reason, at_action } => {
                FireOutcome::Refused { reason, at_action }
            }
            // The world is suspended (meta-debug): the turn staged, it did not fire.
            CommitOutcome::Queued { .. } => FireOutcome::Refused {
                reason: "world suspended: turn queued, not fired".to_string(),
                at_action: vec![],
            },
        }
    }
}

// ===========================================================================
// THE FRUSTUM-SNAPSHOT — the deos-only novelty (rehydration), made real.
// ===========================================================================

/// A **frustum-snapshot** of an affordance surface — the deos rehydration thesis.
///
/// `docs/deos/DEOS.md`: "a deos screenshot embeds a cap-handle behind a membrane,
/// so opening the image re-attaches a live, per-viewer, attenuated interactive
/// surface." A normal screenshot is a dead pixel grid; a deos snapshot is a paused
/// camera on a witnessed *interactive* scene that re-expands inside its own jail.
///
/// It is **tiny** by construction: it carries the surface's backing `cell` + the
/// **culling boundary** (the declared affordance names) — NOT the affordance data,
/// and NOT any viewer's projection. [`AffordanceSnapshot::rehydrate_for`]
/// re-expands it PER-VIEWER by re-projecting through the REAL `is_attenuation` gate
/// (a viewer with a narrow window cap rehydrates a NARROW interactive surface; a
/// wide holder rehydrates a wide one — from the SAME snapshot). The snapshot itself
/// confers NO authority: it names the surface (a "sturdyref"); the rehydration is
/// gated by the WINDOW CAP the viewer presents, exactly like the live `project_for`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffordanceSnapshot {
    /// The surface's backing cell — the cap-handle ("sturdyref") the snapshot
    /// embeds. Naming a cell is NOT authority over it (rehydration is cap-gated).
    pub cell: CellId,
    /// The culling boundary: the declared affordance names at snapshot time (the
    /// frustum), NOT their data. A viewer rehydrates the SUBSET its caps authorize.
    pub affordance_names: Vec<String>,
}

/// The result of rehydrating a snapshot for a specific viewer — the live,
/// per-viewer, attenuated interactive surface the frustum re-expands into.
#[derive(Clone, Debug)]
pub struct Rehydration {
    /// The backing cell (the rehydrated surface's anchor).
    pub cell: CellId,
    /// The affordances the viewer's window cap authorizes (the re-expanded,
    /// attenuated frustum) — ready to render + fire (each through the real
    /// executor via [`AffordanceSurface::fire`] → [`AffordanceIntent::fire_through_world`]).
    pub affordances: Vec<CellAffordance>,
}

impl Rehydration {
    /// The names the viewer rehydrated (sorted) — the per-viewer interactive set.
    pub fn names(&self) -> Vec<String> {
        let mut n: Vec<String> = self.affordances.iter().map(|a| a.name.clone()).collect();
        n.sort();
        n
    }
}

impl AffordanceSurface {
    /// Take a tiny **frustum-snapshot** of this surface — the cell + the declared
    /// names (the culling boundary), NOT the data nor any viewer's projection.
    pub fn snapshot(&self) -> AffordanceSnapshot {
        AffordanceSnapshot {
            cell: self.cell,
            affordance_names: self.affordances.iter().map(|a| a.name.clone()).collect(),
        }
    }
}

impl AffordanceSnapshot {
    /// **Rehydrate** this snapshot for a viewer holding window cap `held`, against
    /// the LIVE surface `surface` (the witness-graph the sturdyref points into).
    ///
    /// The frustum re-expands PER-VIEWER: only the affordances that (a) are still
    /// within the snapshot's boundary (`affordance_names`) AND (b) the viewer's
    /// window cap authorizes (the REAL `is_attenuation`) come back live. Two viewers
    /// rehydrate DIFFERENT surfaces from the SAME snapshot (attenuated rehydration);
    /// a viewer holding nothing rehydrates an EMPTY surface (the snapshot confers no
    /// authority). The live surface is the source of truth, so a snapshot taken
    /// before an affordance was removed rehydrates only what STILL exists.
    pub fn rehydrate_for(
        &self,
        surface: &AffordanceSurface,
        held: &SurfaceCapability,
    ) -> Rehydration {
        let affordances = surface
            .project_for(held)
            .into_iter()
            // Confine to the snapshot's frustum (names captured at snapshot time).
            .filter(|a| self.affordance_names.contains(&a.name))
            .collect();
        Rehydration {
            cell: self.cell,
            affordances,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::SurfaceCapability;
    use dregg_firmament::{AuthRequired as FAuth, Capability};

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    /// A window cap over `backing` carrying `rights` (the firmament surface cap the
    /// shell mints — a window IS this).
    fn window_cap(backing: CellId, rights: FAuth) -> SurfaceCapability {
        SurfaceCapability::new(crate::surface::SurfaceId(1), Capability::surface(backing, rights))
    }

    #[test]
    fn projection_is_progressive_attenuation() {
        // The gate is `is_attenuation(held, required)` = `required ⊆ held` = the
        // viewer must hold AT LEAST `required`. On the AuthRequired lattice,
        // `Signature`/`Proof` are NARROWER than `Either` (the widest), so a
        // `view` affordance any signer holds requires the NARROW `Signature`, and
        // an `admin` affordance requires the WIDER `Either`.
        let backing = cid(0x10);
        let surf = AffordanceSurface::new(backing)
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature, // a narrow requirement — any signer clears it
                Effect::IncrementNonce { cell: backing },
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::Either, // requires the WIDER authority
                Effect::EmitEvent {
                    cell: backing,
                    event: dregg_turn::action::Event::new([0u8; 32], vec![]),
                },
            ));

        // A WIDE holder (Either) sees BOTH: Signature⊆Either ✓ and Either⊆Either ✓.
        let wide = window_cap(backing, FAuth::Either);
        assert_eq!(surf.visible_names(&wide), vec!["admin", "view"]);

        // A NARROW holder (Signature) sees ONLY `view`: Signature⊆Signature ✓, but
        // Either⊄Signature so `admin` is culled. The SAME surface, a DIFFERENT
        // projection — progressive attenuation, by the real is_attenuation.
        let narrow = window_cap(backing, FAuth::Signature);
        assert_eq!(surf.visible_names(&narrow), vec!["view"]);
    }

    #[test]
    fn fire_refuses_an_unauthorized_actor_the_anti_ghost_tooth() {
        let backing = cid(0x20);
        let surf = AffordanceSurface::new(backing).declare(CellAffordance::new(
            "admin",
            AuthRequired::Either,
            Effect::IncrementNonce { cell: backing },
        ));
        // A narrow window cap (Signature) CANNOT fire the `admin` affordance
        // (Either ⊄ Signature) — refused by the real is_attenuation, never run.
        let narrow = window_cap(backing, FAuth::Signature);
        let err = surf.fire("admin", cid(0x21), &narrow).unwrap_err();
        assert_eq!(
            err,
            FireError::Unauthorized {
                affordance: "admin".to_string(),
                required: AuthRequired::Either
            }
        );
        // An unknown affordance name is its own refusal.
        assert_eq!(surf.fire("nope", cid(0x21), &narrow).unwrap_err(), FireError::NoSuchAffordance);
    }

    #[test]
    fn fire_through_world_commits_a_real_verified_turn() {
        // THE SEAM, CLOSED: an authorized fire runs through the embedded executor
        // and produces the executor's OWN receipt — not a modeled dispatch.
        let mut world = World::new();
        // Two real cells in the live ledger; the actor will transfer to the sink.
        let actor = world.genesis_cell(0x30, 5_000);
        let sink = world.genesis_cell(0x31, 0);

        // A surface over `actor` declaring a `pay` affordance — a real Transfer.
        // It requires `Signature` (a narrow right the wide `Either` holder clears,
        // since Signature ⊆ Either).
        let surf = AffordanceSurface::new(actor).declare(CellAffordance::new(
            "pay",
            AuthRequired::Signature,
            Effect::Transfer { from: actor, to: sink, amount: 250 },
        ));
        // The operator holds a wide window cap over `actor`.
        let cap = window_cap(actor, FAuth::Either);

        // Fire → intent (authorized) → through the REAL executor.
        let intent = surf.fire("pay", actor, &cap).expect("authorized");
        assert_eq!(
            intent.effect_summary(),
            EffectSummary::Transfer { from: actor, to: sink, amount: 250 }
        );
        let outcome = intent.fire_through_world(&mut world);
        assert!(outcome.is_committed(), "the embedded executor committed the affordance's turn");

        // The value MOVED — conservation held, the real ledger updated.
        assert_eq!(world.ledger().get(&actor).unwrap().state.balance(), 4_750);
        assert_eq!(world.ledger().get(&sink).unwrap().state.balance(), 250);
        // It left a real receipt in the provenance log (the executor's own).
        assert_eq!(world.receipts().len(), 1);
    }

    #[test]
    fn fire_through_world_surfaces_the_executors_refusal() {
        // The verification axis VISIBLE: an affordance whose effect would BREAK a
        // guarantee is REFUSED by the embedded executor (not by us) when fired —
        // an over-transfer (spend more than the actor holds) cannot commit.
        let mut world = World::new();
        let actor = world.genesis_cell(0x40, 100); // holds only 100
        let sink = world.genesis_cell(0x41, 0);
        let surf = AffordanceSurface::new(actor).declare(CellAffordance::new(
            "overspend",
            AuthRequired::Signature,
            Effect::Transfer { from: actor, to: sink, amount: 1_000_000 },
        ));
        let cap = window_cap(actor, FAuth::Either);
        // The GATE passes (the actor holds the window cap) — but the executor
        // REJECTS the turn (non-conservation / insufficient balance). Both gates
        // are real: the cap gate admits the fire, the executor refuses the turn.
        let intent = surf.fire("overspend", actor, &cap).expect("cap gate admits");
        let outcome = intent.fire_through_world(&mut world);
        assert!(!outcome.is_committed(), "the executor refused the overspend");
        // Nothing moved; no receipt was appended.
        assert_eq!(world.ledger().get(&actor).unwrap().state.balance(), 100);
        assert_eq!(world.receipts().len(), 0);
    }

    #[test]
    fn snapshot_rehydrates_per_viewer_attenuated() {
        // THE FRUSTUM-SNAPSHOT: a tiny snapshot (cell + names) re-expands PER VIEWER
        // through the real is_attenuation gate — two viewers rehydrate DIFFERENT
        // interactive surfaces from the SAME snapshot.
        let backing = cid(0x50);
        let surf = AffordanceSurface::new(backing)
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                Effect::IncrementNonce { cell: backing },
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::Either,
                Effect::IncrementNonce { cell: backing },
            ));
        // The snapshot is tiny: it carries only the cell + the names (the frustum),
        // NOT the affordance data nor any projection.
        let snap = surf.snapshot();
        assert_eq!(snap.cell, backing);
        assert_eq!(snap.affordance_names.len(), 2);

        // A WIDE holder rehydrates BOTH; a NARROW holder rehydrates only `view` —
        // attenuated rehydration from the SAME snapshot.
        let wide = window_cap(backing, FAuth::Either);
        let narrow = window_cap(backing, FAuth::Signature);
        assert_eq!(snap.rehydrate_for(&surf, &wide).names(), vec!["admin", "view"]);
        assert_eq!(snap.rehydrate_for(&surf, &narrow).names(), vec!["view"]);

        // A snapshot whose live surface DROPPED an affordance rehydrates only what
        // STILL exists (the live surface is the source of truth, not the snapshot).
        let shrunk = AffordanceSurface::new(backing).declare(CellAffordance::new(
            "view",
            AuthRequired::Signature,
            Effect::IncrementNonce { cell: backing },
        ));
        // The OLD snapshot still names `admin`, but the live (shrunk) surface no
        // longer has it — so even a wide holder rehydrates only `view`.
        assert_eq!(snap.rehydrate_for(&shrunk, &wide).names(), vec!["view"]);
    }
}
