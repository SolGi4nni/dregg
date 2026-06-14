//! Cell affordances — **htmx on crack**, made into steel. The deos interaction
//! model: a cell declares named, typed **affordances** (effect-TEMPLATES), and
//! rendering / firing one is a **capability-gated verified turn**. Plus the
//! **frustum-snapshot**: a tiny frame embedding a [`Sturdyref`] that
//! rehydrates per-viewer into the live interactive surface.
//!
//! `docs/deos/DEOS.md` — the brand's "htmx-on-crack" thesis: in htmx an element
//! declares `hx-post="/x"` and the server returns a fragment; in deos a **cell
//! declares affordances** — named effect-templates — and an interaction is a
//! **verified turn**: the "button" is a cap-gated [`dregg_turn::Effect`], and *who
//! may press it* is decided by **held capabilities**, not a session cookie.
//! Progressive enhancement becomes progressive **attenuation**: an agent sees
//! exactly the affordances its caps authorize.
//!
//! This module ships the three load-bearing pieces, each on the REAL dregg cap +
//! attestation + membrane discipline the rest of the crate already names — never a
//! new gate, never a parallel cap model, never a stub effect:
//!
//! 1. [`CellAffordance`] — the htmx-on-crack element: a named operation + the
//!    rights it requires ([`AuthRequired`]) + the **effect it would fire** (a real
//!    [`dregg_turn::Effect`], the turn the executor would run). [`AffordanceSurface`]
//!    is a cell's published set of these. The KEY property: a viewer
//!    **sees/may-fire** an affordance ONLY if their held caps satisfy
//!    `required_rights` — checked by the GENUINE [`dregg_cell::is_attenuation`]
//!    (`required ⊆ held`), the SAME gate `delegate.rs` / `rehydrate.rs` run.
//!
//! 2. [`AffordanceSurface::project_for`] — the per-viewer projection: returns ONLY
//!    the affordances a viewer's [`Membrane`] authorizes. Two viewers with
//!    different caps get DIFFERENT affordance sets over the SAME surface
//!    (progressive *attenuation*). Anti-ghost: [`AffordanceSurface::fire`] REFUSES
//!    a viewer firing an affordance they lack the rights for — the same
//!    `is_attenuation` tooth, never an out-of-band check.
//!
//! 3. [`AffordanceSnapshot`] + [`rehydrate_affordances`] — the frustum-snapshot.
//!    The snapshot is **tiny**: a [`Sturdyref`] (the cap-handle, from
//!    [`crate::rehydrate`]) + the culling boundary — NOT the affordance data.
//!    [`rehydrate_affordances`] re-expands the frustum PER-VIEWER through the
//!    EXISTING [`Membrane`] and attaches the derived [`Rehydration`] liveness-type.
//!    This is the frustum-cull made real: the snapshot is a paused camera on a
//!    witnessed interactive scene that re-expands inside its own jail.
//!
//! ## What is real vs. the seam
//!
//! - **Real (the cap discipline + the effect-template + the membrane):** the gate
//!   is the GENUINE [`is_attenuation`] (`required ⊆ held`) — the proven lattice, the
//!   same one the cap crown proves and the membrane composes; the effect-template is
//!   a real [`dregg_turn::Effect`] (a `SetField` / `EmitEvent` / `GrantCapability` —
//!   the exact effect the `TurnExecutor` runs); the snapshot embeds a real
//!   [`Sturdyref`] and rehydrates through the real [`Membrane`] / [`rehydrate`].
//! - **The seam (named, not papered): the firing → executed turn.** Firing an
//!   authorized affordance produces an [`AffordanceIntent`] — the instantiated
//!   effect-template (the real [`Effect`] + the actor + the gate verdict). Handing
//!   that intent to a live [`dregg_turn::TurnExecutor`] (so the receipt is the
//!   executor's own, chained on the per-agent receipt chain) is the boundary this
//!   crate touches the (mid-HARDSWAP) `turn/` executor at — the SAME seam
//!   `web_of_cells.rs` names for the serve-turn. The effect carried IS the real one;
//!   what is modeled is the *dispatch* of it, exactly as `MockSurface` models the
//!   libservo `WebView`'s dispatch of a gated request. The gate that decides
//!   *whether the turn may fire at all* is the real `is_attenuation`, in-band.

use dregg_cell::is_attenuation;
use dregg_cell::AuthRequired;
use dregg_turn::Effect;
use dregg_types::CellId;

use crate::delegate::SurfaceCapability;
use crate::rehydrate::{rehydrate, Membrane, Rehydration, RehydrateError, Sturdyref};
use crate::web_of_cells::WebOfCells;

/// A single **cell affordance** — the htmx-on-crack element.
///
/// `docs/deos/DEOS.md`: "a cell declares affordances — named, typed
/// effect-templates — and an interaction is a verified turn." This is one such
/// declaration: a `name` (the operation, the deos analogue of htmx's `hx-post`
/// path), the `required_rights` a viewer must HOLD to see/fire it, and the
/// `effect_template` it would fire — a real [`dregg_turn::Effect`], the turn the
/// executor would run.
///
/// The cap-gate is the load-bearing part and it is NOT new: a viewer may render or
/// fire this affordance iff [`CellAffordance::authorized_for`] — which is the
/// GENUINE [`dregg_cell::is_attenuation`] (`required ⊆ held`), the same gate the
/// firmament runs for every capability. No session cookie, no ambient role; *who
/// may press the button* is a function of held capabilities.
///
/// `Effect` does not derive `PartialEq` (it carries STARK proofs / eventual refs),
/// so this struct is identified by its `name` + `required_rights` for equality
/// purposes (an affordance's `name` is unique within a surface); the
/// `effect_template` is compared structurally only where a test needs it, via the
/// stable [`CellAffordance::effect_summary`].
#[derive(Clone, Debug)]
pub struct CellAffordance {
    /// The operation name — the affordance's identity within its surface (the deos
    /// analogue of `hx-post="/comment"`). Unique per [`AffordanceSurface`].
    pub name: String,
    /// The authority a viewer must HOLD to see/fire this affordance. The gate is
    /// `is_attenuation(held, required)` = `required ⊆ held` — the viewer must hold
    /// AT LEAST this much authority. A `view` affordance requires a narrow right
    /// (any authenticated reader holds it); an `admin` affordance requires the
    /// broad root right (only a powerful holder clears it).
    pub required_rights: AuthRequired,
    /// The effect this affordance would FIRE — a real [`dregg_turn::Effect`], the
    /// genuine turn the `TurnExecutor` runs (a `SetField` for an edit, an
    /// `EmitEvent` for a comment, a `GrantCapability` for an admin grant). NOT a
    /// stub: instantiating the template (firing the affordance) yields exactly this
    /// effect, ready to hand to the executor.
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

    /// Is this affordance authorized for a holder of `held` authority?
    ///
    /// THE cap-gate, and it is the REAL one: `is_attenuation(held, required)` =
    /// `required ⊆ held` (the proven attenuation lattice). True iff the holder's
    /// authority is at least as broad as this affordance demands. This is the same
    /// predicate `delegate.rs` runs to admit a child surface and `rehydrate.rs` runs
    /// to compose a reshare — NOT a parallel role check.
    pub fn authorized_for(&self, held: &SurfaceCapability) -> bool {
        is_attenuation(&held.window.rights, &self.required_rights)
    }

    /// A stable, `Eq`-able summary of the effect-template (its variant + the cells
    /// it touches), for diagnostics + tests where two templates must be compared
    /// (the `Effect` enum itself is not `PartialEq`). The summary names the REAL
    /// effect — it is a readout of the genuine template, not a substitute for it.
    pub fn effect_summary(&self) -> EffectSummary {
        EffectSummary::of(&self.effect_template)
    }
}

/// A stable, comparable readout of a [`dregg_turn::Effect`] template — its variant
/// tag + the principal cell(s) it acts on. (The `Effect` enum is not `PartialEq`
/// because some variants carry proofs / eventual refs; this is the
/// equality-friendly projection a test or a UI can compare.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectSummary {
    SetField { cell: CellId, index: usize },
    Transfer { from: CellId, to: CellId, amount: u64 },
    GrantCapability { from: CellId, to: CellId },
    RevokeCapability { cell: CellId, slot: u32 },
    EmitEvent { cell: CellId },
    IncrementNonce { cell: CellId },
    /// Any other real `Effect` variant, tagged by its name (still the genuine
    /// effect — only the *summary* is coarse).
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
        Effect::SetPermissions { .. } => "SetPermissions",
        Effect::SetVerificationKey { .. } => "SetVerificationKey",
        Effect::NoteSpend { .. } => "NoteSpend",
        Effect::NoteCreate { .. } => "NoteCreate",
        Effect::SpawnWithDelegation { .. } => "SpawnWithDelegation",
        Effect::RefreshDelegation => "RefreshDelegation",
        Effect::RevokeDelegation { .. } => "RevokeDelegation",
        Effect::BridgeMint { .. } => "BridgeMint",
        Effect::Introduce { .. } => "Introduce",
        Effect::PipelinedSend { .. } => "PipelinedSend",
        Effect::ExerciseViaCapability { .. } => "ExerciseViaCapability",
        Effect::MakeSovereign { .. } => "MakeSovereign",
        Effect::CreateCellFromFactory { .. } => "CreateCellFromFactory",
        // A catch-all so a HARDSWAP that ADDS an `Effect` variant still compiles
        // here (the new variant summarizes as its Debug-less fallback rather than
        // breaking the build). Any added variant is still the REAL effect.
        _ => "UnknownEffect",
    }
}

/// A cell's published **affordance surface** — the set of affordances it exposes,
/// the deos analogue of a server's set of htmx endpoints.
///
/// `docs/deos/DEOS.md`: "every interactive element is a turn the witness-graph
/// records." This binds a `cell` (the surface's backing object) to its declared
/// `affordances`. Rendering it for a viewer is [`AffordanceSurface::project_for`]
/// (CAP-GATED); firing one is [`AffordanceSurface::fire`] (CAP-GATED, anti-ghost).
#[derive(Clone, Debug)]
pub struct AffordanceSurface {
    /// The cell backing this surface (the object whose affordances these are).
    pub cell: CellId,
    /// The declared affordances. Names are unique (a [`AffordanceSurface::declare`]
    /// with a duplicate name replaces the prior one).
    pub affordances: Vec<CellAffordance>,
}

/// Why a [`AffordanceSurface::fire`] was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FireError {
    /// No affordance by that name on this surface.
    NoSuchAffordance,
    /// The actor's held caps do NOT satisfy the affordance's `required_rights` —
    /// the anti-ghost tooth: a viewer firing an affordance they lack the rights for
    /// is REFUSED by the REAL `is_attenuation`, never silently run.
    Unauthorized {
        /// The affordance the actor tried to fire.
        affordance: String,
        /// The authority it required (which the actor did not hold).
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

    /// All declared affordance names (sorted), regardless of viewer — the full
    /// surface, for diagnostics.
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
    /// holder of `held` authority is authorized to see/fire — progressive
    /// enhancement becomes progressive **attenuation**.
    ///
    /// `docs/deos/DEOS.md`: "an agent sees exactly the affordances its caps
    /// authorize." Each affordance is admitted iff [`CellAffordance::authorized_for`]
    /// — the REAL `is_attenuation` (`required ⊆ held`). Two viewers holding
    /// different caps get DIFFERENT projections of the SAME surface. The order is
    /// preserved (declaration order), so the projection is a stable sub-list.
    pub fn project_for(&self, held: &SurfaceCapability) -> Vec<CellAffordance> {
        self.affordances
            .iter()
            .filter(|a| a.authorized_for(held))
            .cloned()
            .collect()
    }

    /// Convenience: project through a [`Membrane`] (the viewer's held authority is
    /// the membrane's [`Membrane::held`]). The membrane is the crate's existing
    /// enforcer; an affordance surface uses the SAME held-authority it carries.
    pub fn project_for_membrane(&self, membrane: &Membrane) -> Vec<CellAffordance> {
        self.project_for(membrane.held())
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

    /// **Fire** the affordance named `name` as an actor holding `held` authority,
    /// from `actor` cell.
    ///
    /// The htmx-on-crack interaction: pressing the "button" produces a
    /// **verified-turn intent** — the effect-template instantiated. The gate is
    /// in-band and REAL: the fire is admitted iff the actor's `held` authority
    /// satisfies the affordance's `required_rights` ([`CellAffordance::authorized_for`]
    /// = `is_attenuation`). The **anti-ghost tooth**: an actor firing an affordance
    /// they lack the rights for is [`FireError::Unauthorized`] — REFUSED, never run.
    ///
    /// On success returns an [`AffordanceIntent`] carrying the REAL
    /// [`dregg_turn::Effect`] the executor would run. Handing that to a live
    /// `TurnExecutor` is the named seam (see the module-level `## the seam`); the
    /// effect IS the genuine one, and whether it may fire AT ALL is decided here,
    /// by the proven gate.
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

    /// Fire through a [`Membrane`] (actor's held authority = the membrane's held).
    pub fn fire_through(
        &self,
        name: &str,
        actor: CellId,
        membrane: &Membrane,
    ) -> Result<AffordanceIntent, FireError> {
        self.fire(name, actor, membrane.held())
    }
}

/// The **verified-turn intent** firing an authorized affordance produces — the
/// effect-template instantiated, ready for the executor.
///
/// `docs/deos/DEOS.md`: "the 'button' is a cap-gated effect … every interactive
/// element is a turn the witness-graph records." This is that turn, before
/// dispatch: the REAL [`dregg_turn::Effect`] the affordance fires, the `actor`
/// firing it, and the `surface_cell` it acts on. It is ONLY ever minted by
/// [`AffordanceSurface::fire`] AFTER the real `is_attenuation` gate passed — so an
/// intent's existence witnesses that the actor was authorized. Handing
/// [`AffordanceIntent::effect`] to a live `TurnExecutor` is the named seam.
#[derive(Clone, Debug)]
pub struct AffordanceIntent {
    /// The cell whose affordance was fired (the surface's backing cell).
    pub surface_cell: CellId,
    /// The affordance name that was fired.
    pub affordance: String,
    /// The actor cell that fired it (the principal of the turn).
    pub actor: CellId,
    /// The REAL effect the turn would run — the instantiated effect-template. Hand
    /// this to a `TurnExecutor` to execute the turn (the named seam).
    pub effect: Effect,
}

impl AffordanceIntent {
    /// The `Eq`-able summary of the effect this intent would run (the `Effect` is
    /// not `PartialEq`). Names the REAL effect.
    pub fn effect_summary(&self) -> EffectSummary {
        EffectSummary::of(&self.effect)
    }
}

/// A **frustum-snapshot** of an affordance surface — THE dregg-only novelty,
/// made real.
///
/// `docs/deos/DEOS.md`: "a deos screenshot is a frame of the certified compositor
/// over the witness-graph; it embeds a sturdyref behind a membrane, so opening the
/// image re-attaches a live, per-viewer, attenuated, liveness-typed interactive
/// surface." This is that snapshot, and it is **tiny** by construction: it carries
/// a [`Sturdyref`] (the cap-handle into the witness-graph, from
/// [`crate::rehydrate`]) + the **culling boundary** (the cell + the surface's
/// declared affordance names) — NOT the affordance data itself, and NOT any
/// viewer's projection. A normal screenshot is a dead pixel grid; a deos snapshot
/// is a paused camera on a witnessed *interactive* scene that re-expands inside its
/// own jail.
///
/// The re-expansion is [`rehydrate_affordances`]: per-viewer, membrane-negotiated,
/// liveness-typed. The snapshot is the same `kind` of cheap-to-ship object as a
/// PNG; the substance is the attested per-viewer re-expansion of a certified
/// projection of a witnessed interactive scene.
#[derive(Clone, Debug)]
pub struct AffordanceSnapshot {
    /// The embedded **sturdyref** — the cap-handle into the witness-graph (the
    /// `dregg://` ref + the publisher's authority lineage + the witness-log). This
    /// is what makes the snapshot rehydratable: handed to someone cold, it
    /// re-establishes the connection.
    pub sturdyref: Sturdyref,
    /// The **culling boundary** — the surface's backing cell + the declared
    /// affordance names. This is the frustum: it bounds WHAT could be re-expanded,
    /// without embedding the affordances' effect-templates or any viewer's
    /// projection. (The full affordance set is re-derived at the surface, gated
    /// per-viewer, at rehydration — the snapshot only names the boundary.)
    pub boundary: SurfaceBoundary,
}

/// The culling boundary a [`AffordanceSnapshot`] embeds — the cell + the affordance
/// names that bound the frustum, WITHOUT the effect-templates (those live at the
/// surface, re-derived per-viewer on rehydration).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceBoundary {
    /// The surface's backing cell.
    pub cell: CellId,
    /// The names of the affordances the surface declares (the frustum extent).
    /// Sorted, so the boundary is canonical.
    pub affordance_names: Vec<String>,
}

impl AffordanceSnapshot {
    /// Take a frustum-snapshot of `surface`, embedding `sturdyref`. The snapshot
    /// records only the culling boundary (cell + affordance names) — it is tiny by
    /// construction: it does NOT carry the effect-templates or any projection.
    ///
    /// `sturdyref.uri.cell` SHOULD denote `surface.cell` (the snapshot is of THIS
    /// surface); we record the surface's cell in the boundary so rehydration can
    /// cross-check.
    pub fn take(surface: &AffordanceSurface, sturdyref: Sturdyref) -> Self {
        AffordanceSnapshot {
            sturdyref,
            boundary: SurfaceBoundary {
                cell: surface.cell,
                affordance_names: surface.all_names(),
            },
        }
    }

    /// The number of affordance names in the frustum boundary (the extent of what
    /// could re-expand) — a scalar readout that the snapshot is tiny (it grows with
    /// the NAME count, never the effect-template payloads).
    pub fn boundary_extent(&self) -> usize {
        self.boundary.affordance_names.len()
    }
}

/// **Rehydrate** a [`AffordanceSnapshot`] PER-VIEWER into the live interactive
/// surface — the frustum-cull made real.
///
/// `docs/deos/DEOS.md`: "opening the image re-attaches a live, per-viewer,
/// attenuated, liveness-typed interactive surface." This is that re-attachment, and
/// it composes the EXISTING rehydration stack with the affordance gate:
///
/// 1. **fetch = verified turn returning attested content + the per-viewer
///    projection** — run the REAL [`rehydrate`] over the snapshot's sturdyref + the
///    viewer's [`Membrane`]. This (a) VERIFIES the attested scene (an unattested
///    scene yields NO surface, regardless of caps — confinement before relation),
///    and (b) derives the viewer's [`crate::rehydrate::Projection`] = `(held) ∧
///    (lineage)` through the proven lattice, and (c) the [`Rehydration`]
///    liveness-type. A failure here ([`RehydrateError`]) means NO interactive
///    surface re-expands.
/// 2. **per-viewer affordance projection** — re-derive `surface`'s affordances
///    gated by what the viewer's membrane authorizes ([`AffordanceSurface::project_for_membrane`]),
///    the SAME `is_attenuation` gate. Two viewers re-expand the SAME snapshot to
///    DIFFERENT live affordance sets.
/// 3. **the liveness-type carries through** — returned alongside the affordances, so
///    the re-expanded interactive surface is typed (LIVE / REPLAYED-DETERMINISTIC /
///    RECONSTRUCTED-APPROXIMATE) exactly as a rehydrated *view* is.
///
/// `surface` is the live surface the snapshot's boundary named (re-supplied at
/// rehydration time — the snapshot embedded only the boundary, not the
/// effect-templates). We cross-check that `surface.cell` matches the snapshot's
/// boundary cell; a mismatch is [`RehydrateError::Fetch`]-shaped only if the fetch
/// itself fails, so we surface a boundary mismatch as its own error.
pub fn rehydrate_affordances(
    snapshot: &AffordanceSnapshot,
    surface: &AffordanceSurface,
    membrane: &Membrane,
    web: &WebOfCells,
) -> Result<(Vec<CellAffordance>, Rehydration), AffordanceRehydrateError> {
    // The supplied live surface must be the one the snapshot's frustum bounded.
    if surface.cell != snapshot.boundary.cell {
        return Err(AffordanceRehydrateError::BoundaryMismatch);
    }
    // (1) The REAL rehydration: verify the attested scene + derive the per-viewer
    //     projection + the liveness-type. Confinement before relation — an
    //     unattested scene re-expands to nothing, regardless of caps.
    let projection = rehydrate(&snapshot.sturdyref, membrane, web)
        .map_err(AffordanceRehydrateError::Rehydrate)?;

    // (2) The per-viewer affordance projection through the SAME membrane / the SAME
    //     is_attenuation gate. The frustum re-expands per-viewer.
    let affordances = surface.project_for_membrane(membrane);

    // (3) The liveness-type carries through, derived from the source context's
    //     witness-log (LIVE / REPLAYED-DETERMINISTIC / RECONSTRUCTED-APPROXIMATE).
    Ok((affordances, projection.liveness))
}

/// Why a [`rehydrate_affordances`] failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AffordanceRehydrateError {
    /// The supplied live surface is not the one the snapshot's frustum bounded
    /// (its cell ≠ the boundary cell) — you cannot rehydrate a snapshot against a
    /// different surface.
    BoundaryMismatch,
    /// The underlying [`rehydrate`] failed: the attested scene did not verify (no
    /// surface re-expands — confinement before relation), or the membrane refused
    /// the projection (amplification). Carries the real [`RehydrateError`].
    Rehydrate(RehydrateError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rehydrate::InteractionLog;
    use crate::web_of_cells::DreggUri;
    use std::collections::BTreeSet;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn origins(list: &[&str]) -> BTreeSet<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    /// A real `SetField` effect (the genuine turn the executor runs for an edit).
    fn set_field(cell: CellId, index: usize) -> Effect {
        Effect::SetField {
            cell,
            index,
            value: [7u8; 32], // a real FieldElement ([u8;32])
        }
    }

    /// A real `EmitEvent` effect (the genuine turn for a comment/log).
    fn emit_event(cell: CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: dregg_turn::Event {
                topic: [1u8; 32],
                data: vec![],
            },
        }
    }

    /// A real `GrantCapability` effect (the genuine turn for an admin grant).
    fn grant_cap(from: CellId, to: CellId) -> Effect {
        Effect::GrantCapability {
            from,
            to,
            cap: dregg_cell::CapabilityRef {
                target: to,
                slot: 0,
                permissions: AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        }
    }

    /// The canonical four-affordance DOC-cell surface used across the tests + the
    /// demo: {view, comment, edit, admin} on a clean three-tier rights chain
    /// `Signature ⊂ Either ⊂ None` — view at tier-1, comment+edit at tier-2, admin
    /// at tier-3. Each carries a REAL effect-template.
    fn doc_surface(doc: CellId) -> AffordanceSurface {
        AffordanceSurface::new(doc)
            // view: the weakest meaningful right — any authenticated reader.
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                emit_event(doc), // a read logs an access event (a real turn)
            ))
            // comment: the editor tier (Either ⊃ Signature).
            .declare(CellAffordance::new(
                "comment",
                AuthRequired::Either,
                emit_event(doc),
            ))
            // edit: the editor tier too — writes a state field.
            .declare(CellAffordance::new(
                "edit",
                AuthRequired::Either,
                set_field(doc, 1),
            ))
            // admin: the broad root tier (None) — grants a capability.
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None,
                grant_cap(doc, cid(99)),
            ))
    }

    // viewer holds tier-1 (Signature); editor holds tier-2 (Either); admin holds
    // tier-3 (None / root).
    fn viewer_held() -> SurfaceCapability {
        SurfaceCapability::root(cid(10), AuthRequired::Signature)
    }
    fn editor_held() -> SurfaceCapability {
        SurfaceCapability::root(cid(11), AuthRequired::Either)
    }
    fn admin_held() -> SurfaceCapability {
        SurfaceCapability::root(cid(12), AuthRequired::None)
    }

    // ── Property 1: the affordance is the htmx-on-crack element on a REAL effect,
    //    cap-gated by the REAL is_attenuation. ──

    #[test]
    fn an_affordance_carries_a_real_effect_template() {
        // Anti-toy: the effect_template IS a real dregg_turn::Effect — the genuine
        // turn the executor would run, not a stub.
        let doc = cid(1);
        let edit = CellAffordance::new("edit", AuthRequired::Either, set_field(doc, 3));
        assert_eq!(
            edit.effect_summary(),
            EffectSummary::SetField { cell: doc, index: 3 }
        );
        // And it really is the `Effect` type (matchable as the genuine enum).
        assert!(matches!(edit.effect_template, Effect::SetField { .. }));
    }

    #[test]
    fn the_cap_gate_is_the_real_is_attenuation() {
        // THE gate: authorized_for == is_attenuation(held, required) == required ⊆
        // held. A viewer holding Signature clears a view (req Signature) but NOT an
        // admin (req None / root). This is the SAME predicate the firmament runs.
        let doc = cid(1);
        let view = CellAffordance::new("view", AuthRequired::Signature, emit_event(doc));
        let admin = CellAffordance::new("admin", AuthRequired::None, grant_cap(doc, cid(99)));

        // The gate agrees with is_attenuation by construction, both polarities.
        assert!(view.authorized_for(&viewer_held()));
        assert_eq!(
            view.authorized_for(&viewer_held()),
            is_attenuation(&viewer_held().window.rights, &AuthRequired::Signature)
        );
        assert!(!admin.authorized_for(&viewer_held()));
        assert_eq!(
            admin.authorized_for(&viewer_held()),
            is_attenuation(&viewer_held().window.rights, &AuthRequired::None)
        );
        // The admin (root) holder clears the admin affordance.
        assert!(admin.authorized_for(&admin_held()));
    }

    // ── Property 2: the per-viewer projection — progressive attenuation. Two
    //    viewers DIVERGE over the SAME surface. ──

    #[test]
    fn two_viewers_with_different_caps_see_different_affordance_sets() {
        // THE deos property: the viewer sees {view}; the editor sees
        // {comment, edit, view}; over the SAME surface. Progressive enhancement is
        // progressive ATTENUATION.
        let doc = cid(2);
        let surface = doc_surface(doc);

        let viewer_set = surface.visible_names(&viewer_held());
        let editor_set = surface.visible_names(&editor_held());
        let admin_set = surface.visible_names(&admin_held());

        assert_eq!(viewer_set, vec!["view".to_string()]);
        assert_eq!(
            editor_set,
            vec!["comment".to_string(), "edit".to_string(), "view".to_string()]
        );
        assert_eq!(
            admin_set,
            vec![
                "admin".to_string(),
                "comment".to_string(),
                "edit".to_string(),
                "view".to_string()
            ]
        );

        // DIVERGENCE: the sets are genuinely different over the SAME surface.
        assert_ne!(viewer_set, editor_set);
        assert_ne!(editor_set, admin_set);
        // And the projection is monotone in authority: viewer ⊂ editor ⊂ admin.
        assert!(viewer_set.iter().all(|n| editor_set.contains(n)));
        assert!(editor_set.iter().all(|n| admin_set.contains(n)));
    }

    #[test]
    fn project_for_returns_only_authorized_affordances() {
        // Every affordance in a projection is authorized for the viewer; none
        // outside it is — the projection IS exactly the gated set.
        let doc = cid(3);
        let surface = doc_surface(doc);
        let proj = surface.project_for(&editor_held());

        for a in &proj {
            assert!(a.authorized_for(&editor_held()));
        }
        // admin is NOT in the editor's projection (editor lacks root).
        assert!(!proj.iter().any(|a| a.name == "admin"));
        // every authorized affordance IS present (view, comment, edit).
        for name in ["view", "comment", "edit"] {
            assert!(proj.iter().any(|a| a.name == name), "{name} must be visible to editor");
        }
    }

    // ── Property 2 anti-ghost: firing an unauthorized affordance is REFUSED. ──

    #[test]
    fn firing_an_authorized_affordance_yields_the_real_turn_intent() {
        // The viewer fires `view` (authorized): an intent carrying the REAL effect.
        let doc = cid(4);
        let surface = doc_surface(doc);
        let intent = surface
            .fire("view", cid(50), &viewer_held())
            .expect("an authorized fire yields an intent");
        assert_eq!(intent.actor, cid(50));
        assert_eq!(intent.surface_cell, doc);
        assert_eq!(intent.affordance, "view");
        // The intent carries the REAL effect the executor would run.
        assert_eq!(intent.effect_summary(), EffectSummary::EmitEvent { cell: doc });
        assert!(matches!(intent.effect, Effect::EmitEvent { .. }));
    }

    #[test]
    fn firing_an_unauthorized_affordance_is_refused_anti_ghost() {
        // THE anti-ghost tooth: the viewer (Signature) tries to fire `admin`
        // (req None / root). REFUSED by the SAME is_attenuation gate — never run.
        let doc = cid(5);
        let surface = doc_surface(doc);
        let refused = surface.fire("admin", cid(50), &viewer_held());
        assert_eq!(
            refused.unwrap_err(),
            FireError::Unauthorized {
                affordance: "admin".to_string(),
                required: AuthRequired::None,
            }
        );

        // The editor (Either) ALSO cannot fire admin (lacks root).
        assert!(matches!(
            surface.fire("admin", cid(51), &editor_held()),
            Err(FireError::Unauthorized { .. })
        ));
        // But the admin (root) CAN — yielding the real GrantCapability turn.
        let admin_intent = surface
            .fire("admin", cid(52), &admin_held())
            .expect("admin holder fires admin");
        assert_eq!(
            admin_intent.effect_summary(),
            EffectSummary::GrantCapability { from: doc, to: cid(99) }
        );
    }

    #[test]
    fn firing_a_missing_affordance_is_no_such_affordance() {
        let surface = doc_surface(cid(6));
        assert_eq!(
            surface.fire("nonexistent", cid(50), &admin_held()).unwrap_err(),
            FireError::NoSuchAffordance
        );
    }

    #[test]
    fn the_gate_refuses_a_viewer_who_holds_an_incomparable_right() {
        // A holder of `Proof` is INCOMPARABLE to `Either` (neither ⊆ the other), so
        // an Either-tier affordance is refused — the gate is the real lattice, not a
        // numeric rank. (Proof clears `view`@Signature? No: Signature ⊄ Proof and
        // Proof ⊄ Signature — incomparable. So a Proof holder sees NEITHER view nor
        // comment — only affordances requiring None or Proof or Impossible.)
        let doc = cid(7);
        let surface = doc_surface(doc);
        let proof_held = SurfaceCapability::root(cid(13), AuthRequired::Proof);
        // view requires Signature: Signature ⊄ Proof → refused.
        assert!(!surface.get("view").unwrap().authorized_for(&proof_held));
        // comment/edit require Either: Either ⊄ Proof → refused.
        assert!(!surface.get("comment").unwrap().authorized_for(&proof_held));
        // The Proof holder sees NOTHING on this doc surface.
        assert!(surface.visible_names(&proof_held).is_empty());
    }

    // ── Property 3: the frustum-snapshot → rehydrate-to-live. ──

    /// Publish the doc surface's backing cell into a real web-of-cells and build a
    /// sturdyref over it (carrying a lineage + a confined witness-log), returning
    /// `(web, surface, snapshot)`. The snapshot is the frustum frame.
    fn snapshot_of_doc(
        seed: u8,
        lineage_rights: AuthRequired,
        log: InteractionLog,
        sources_reachable: bool,
    ) -> (WebOfCells, AffordanceSurface, AffordanceSnapshot) {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(seed, b"<h1>a doc cell with affordances</h1>", "dregg://doc");
        let surface = doc_surface(uri.cell);
        let lineage = SurfaceCapability::root(uri.cell, lineage_rights);
        let sturdyref = Sturdyref::new(uri, lineage, log, sources_reachable);
        let snapshot = AffordanceSnapshot::take(&surface, sturdyref);
        (web, surface, snapshot)
    }

    fn a_real_witness() -> dregg_types::AttestedRoot {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(200, b"witnessed turn", "dregg://w");
        let (resource, _chrome) = web.fetch(&uri).expect("fetch resolves");
        assert!(resource.verify().is_ok());
        resource.attested_root
    }

    #[test]
    fn the_snapshot_is_tiny_a_sturdyref_plus_the_boundary_not_the_data() {
        // The frustum-snapshot embeds a Sturdyref + the culling boundary (cell +
        // affordance NAMES), NOT the effect-templates. Its extent grows with the
        // name count, never the effect payloads — it is tiny by construction.
        let (_web, surface, snapshot) = snapshot_of_doc(
            10,
            AuthRequired::None,
            InteractionLog::new(),
            false,
        );
        // The boundary names exactly the surface's affordances (sorted).
        assert_eq!(snapshot.boundary.affordance_names, surface.all_names());
        assert_eq!(snapshot.boundary_extent(), 4); // view/comment/edit/admin
        // It carries the sturdyref (the cap-handle), bound to the surface cell.
        assert_eq!(snapshot.sturdyref.uri.cell, surface.cell);
        assert_eq!(snapshot.boundary.cell, surface.cell);
        // Crucially the snapshot does NOT carry the effect-templates: the boundary
        // is just names. (A structural witness that it is the frustum, not the
        // payload — there is no `Effect` field on `SurfaceBoundary`.)
    }

    #[test]
    fn rehydrate_re_expands_the_frustum_per_viewer() {
        // Two viewers rehydrate the SAME snapshot → DIFFERENT live affordance sets,
        // each membrane-negotiated. The frustum-cull made real.
        let witness = a_real_witness();
        let mut log = InteractionLog::new();
        log.record_attested_fetch(DreggUri::new(cid(60)), witness);
        let (web, surface, snapshot) =
            snapshot_of_doc(11, AuthRequired::None, log, false);

        let viewer = Membrane::new(viewer_held());
        let editor = Membrane::new(editor_held());

        let (viewer_aff, viewer_live) =
            rehydrate_affordances(&snapshot, &surface, &viewer, &web).expect("viewer rehydrates");
        let (editor_aff, editor_live) =
            rehydrate_affordances(&snapshot, &surface, &editor, &web).expect("editor rehydrates");

        let viewer_names: Vec<String> = {
            let mut n: Vec<String> = viewer_aff.iter().map(|a| a.name.clone()).collect();
            n.sort();
            n
        };
        let editor_names: Vec<String> = {
            let mut n: Vec<String> = editor_aff.iter().map(|a| a.name.clone()).collect();
            n.sort();
            n
        };

        // SAME snapshot, DIFFERENT per-viewer re-expansions.
        assert_eq!(viewer_names, vec!["view".to_string()]);
        assert_eq!(
            editor_names,
            vec!["comment".to_string(), "edit".to_string(), "view".to_string()]
        );
        assert_ne!(viewer_names, editor_names);

        // The round-trip matches the direct projection (snapshot→rehydrate is the
        // SAME per-viewer set the surface would project directly).
        assert_eq!(viewer_names, surface.visible_names(&viewer_held()));
        assert_eq!(editor_names, surface.visible_names(&editor_held()));

        // The liveness-type carries through (every interaction witnessed, sources
        // gone → ReplayedDeterministic).
        assert_eq!(viewer_live, Rehydration::ReplayedDeterministic);
        assert_eq!(editor_live, Rehydration::ReplayedDeterministic);
    }

    #[test]
    fn the_liveness_type_carries_through_both_polarities() {
        // The re-expanded interactive surface is TYPED. A confined source replays
        // deterministically; a leaky one reconstructs — DERIVED, carried through.
        let witness = a_real_witness();

        // Confined: every interaction witnessed → ReplayedDeterministic.
        let mut confined = InteractionLog::new();
        confined.record_attested_fetch(DreggUri::new(cid(61)), witness.clone());
        let (web1, surface1, snap1) =
            snapshot_of_doc(12, AuthRequired::None, confined, false);
        let (_aff, live1) =
            rehydrate_affordances(&snap1, &surface1, &Membrane::new(admin_held()), &web1)
                .expect("rehydrates");
        assert_eq!(live1, Rehydration::ReplayedDeterministic);
        assert!(live1.is_faithful());

        // Leaky: one ambient interaction → ReconstructedApproximate.
        let mut leaky = InteractionLog::new();
        leaky.record_attested_fetch(DreggUri::new(cid(62)), witness);
        leaky.record_ambient("raw fetch outside the membrane");
        let (web2, surface2, snap2) =
            snapshot_of_doc(13, AuthRequired::None, leaky, false);
        let (_aff2, live2) =
            rehydrate_affordances(&snap2, &surface2, &Membrane::new(admin_held()), &web2)
                .expect("rehydrates");
        assert_eq!(live2, Rehydration::ReconstructedApproximate);
        assert!(!live2.is_faithful());

        // Live: sources reachable dominates.
        let (web3, surface3, snap3) =
            snapshot_of_doc(14, AuthRequired::None, InteractionLog::new(), true);
        let (_aff3, live3) =
            rehydrate_affordances(&snap3, &surface3, &Membrane::new(admin_held()), &web3)
                .expect("rehydrates");
        assert_eq!(live3, Rehydration::Live);
    }

    #[test]
    fn rehydrating_an_unattested_scene_yields_no_surface_confinement_before_relation() {
        // Confinement before relation: a snapshot whose sturdyref points at a cell
        // that was never published (a dead `dregg://` ref) re-expands to NOTHING,
        // even for a full-authority (admin/root) viewer. The fetch is a verified
        // turn; it fails BEFORE any affordance set is re-derived.
        let web = WebOfCells::new(3);
        let dead_cell = cid(80);
        let surface = doc_surface(dead_cell);
        let dead_ref = Sturdyref::new(
            DreggUri::new(dead_cell),
            SurfaceCapability::root(dead_cell, AuthRequired::None),
            InteractionLog::new(),
            false,
        );
        let snapshot = AffordanceSnapshot::take(&surface, dead_ref);
        // A full-authority viewer still gets NO surface (the scene didn't verify).
        let admin = Membrane::new(admin_held());
        let result = rehydrate_affordances(&snapshot, &surface, &admin, &web);
        assert!(
            matches!(result, Err(AffordanceRehydrateError::Rehydrate(RehydrateError::Fetch(_)))),
            "an unattested scene must yield NO interactive surface even with full caps"
        );
    }

    #[test]
    fn rehydrating_against_the_wrong_surface_is_a_boundary_mismatch() {
        // You cannot rehydrate a snapshot against a DIFFERENT surface than its
        // frustum bounded — the boundary cell cross-check refuses it.
        let (web, _surface, snapshot) = snapshot_of_doc(
            15,
            AuthRequired::None,
            InteractionLog::new(),
            false,
        );
        let other_surface = doc_surface(cid(81)); // a different cell
        let result =
            rehydrate_affordances(&snapshot, &other_surface, &Membrane::new(admin_held()), &web);
        assert_eq!(result.unwrap_err(), AffordanceRehydrateError::BoundaryMismatch);
    }

    // ── Anti-toy seam check: the effect-templates ARE real effects across the
    //    whole doc surface (not a single lucky variant). ──

    #[test]
    fn every_doc_affordance_carries_a_real_distinct_effect_template() {
        let doc = cid(90);
        let surface = doc_surface(doc);
        // view + comment → EmitEvent; edit → SetField; admin → GrantCapability —
        // all REAL dregg_turn::Effect variants, the genuine turns.
        assert_eq!(
            surface.get("view").unwrap().effect_summary(),
            EffectSummary::EmitEvent { cell: doc }
        );
        assert_eq!(
            surface.get("edit").unwrap().effect_summary(),
            EffectSummary::SetField { cell: doc, index: 1 }
        );
        assert_eq!(
            surface.get("admin").unwrap().effect_summary(),
            EffectSummary::GrantCapability { from: doc, to: cid(99) }
        );
        // And each is matchable as the genuine enum (not a parallel stub type).
        assert!(matches!(surface.get("edit").unwrap().effect_template, Effect::SetField { .. }));
        assert!(matches!(surface.get("admin").unwrap().effect_template, Effect::GrantCapability { .. }));
    }

    #[test]
    fn declare_replaces_by_name() {
        // A re-declared affordance (same name) replaces the prior one — names are
        // unique within a surface.
        let doc = cid(91);
        let surface = AffordanceSurface::new(doc)
            .declare(CellAffordance::new("x", AuthRequired::None, emit_event(doc)))
            .declare(CellAffordance::new("x", AuthRequired::Signature, set_field(doc, 0)));
        assert_eq!(surface.affordances.len(), 1);
        // The SECOND declaration won.
        assert_eq!(surface.get("x").unwrap().required_rights, AuthRequired::Signature);
        assert_eq!(
            surface.get("x").unwrap().effect_summary(),
            EffectSummary::SetField { cell: doc, index: 0 }
        );
    }
}
