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
use dregg_cell::state::CellState;
use dregg_cell::AuthRequired;
use dregg_turn::Effect;
use dregg_types::CellId;

use crate::delegate::SurfaceCapability;
use crate::rehydrate::{rehydrate, Membrane, RehydrateError, Rehydration, Sturdyref};
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

// ════════════════════════════════════════════════════════════════════════════
// The TEMPORAL / TRANSITION rung — the Rust mirror of `Dregg2.Deos.Reactive`.
//
// LAW #1: the Lean (`metatheory/Dregg2/Deos/Reactive.lean`) is authoritative;
// this is its faithful Rust twin. `GatedAffordance` (the `app-framework` sibling
// lane) gates a SINGLE state snapshot via a `state_cond` cell-program. This rung
// gates the SHAPE of the `old → new` TRANSITION (a relational `link` reading BOTH
// records — "the tally went up by exactly one", which a property of `new` alone
// can NEVER witness) PLUS an inclusive `[open_height, close_height]` deadline
// WINDOW over the turn height. The membrane (`projectMembrane`) divides a surface
// by BOTH the cap dimension AND a per-viewer witness-graph disclosure bit.
// ════════════════════════════════════════════════════════════════════════════

/// A decidable predicate on a SINGLE record — the `pre`/`post` endpoints of a
/// transition gate. The Rust twin of the Lean `Value → Bool`. (E.g. "the cell's
/// status slot is PENDING".)
pub type RecordPredicate = Box<dyn Fn(&CellState) -> bool>;

/// A decidable predicate on a TRANSITION `(old, new)` — reads BOTH records. The
/// atom of reactivity and the Rust twin of the Lean `TransitionPred`
/// (`Value → Value → Bool`): unlike a single-state predicate, a
/// `TransitionPredicate` can require `new[count] == old[count] + 1` — the
/// relational pre→new bridge the existing single-state `state_cond`
/// (`GatedAffordance`) cannot express by construction.
pub type TransitionPredicate = Box<dyn Fn(&CellState, &CellState) -> bool>;

/// **`TransitionGate`** — a transition gate as three decidable predicates (the
/// Rust twin of the Lean `TransitionGate`): `pre` (the cell must START in a
/// qualifying state — e.g. status = PENDING), `post` (it must LAND in a
/// qualifying state), and `link` (the relational pre→new bridge — the part that
/// reads BOTH records, e.g. "the tally went up by exactly one"). The `link` is
/// what makes this a TRANSITION gate and not two single-state gates: it cannot be
/// witnessed by either endpoint alone — the half a single-state gate
/// (`admitsCtx … old new` read as "is `new` ok") can be fooled by.
pub struct TransitionGate {
    /// The OLD record must satisfy this (the cell starts in a qualifying state).
    pub pre: RecordPredicate,
    /// The NEW record must satisfy this (the cell lands in a qualifying state).
    pub post: RecordPredicate,
    /// The relational pre→new bridge — reads BOTH records (e.g.
    /// `new[count] == old[count] + 1`). The reactivity core: a property of `new`
    /// alone can never witness it.
    pub link: TransitionPredicate,
}

impl std::fmt::Debug for TransitionGate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The predicates are closures (not `Debug`); name the gate's shape, not
        // its (opaque) function pointers.
        f.debug_struct("TransitionGate")
            .field("pre", &"<RecordPredicate>")
            .field("post", &"<RecordPredicate>")
            .field("link", &"<TransitionPredicate>")
            .finish()
    }
}

impl TransitionGate {
    /// Assemble a transition gate from its three predicates.
    pub fn new(pre: RecordPredicate, post: RecordPredicate, link: TransitionPredicate) -> Self {
        TransitionGate { pre, post, link }
    }

    /// **`transition_ok(old, new)`** — the transition gate fires:
    /// `pre(old) && post(new) && link(old, new)`. THE predicate that says "this
    /// `old → new` transition is the one this button reacts to" (the Rust twin of
    /// the Lean `transitionOK`). The conjunction is what makes a property of `new`
    /// alone insufficient: the `link` reaches back into `old`.
    pub fn transition_ok(&self, old: &CellState, new: &CellState) -> bool {
        (self.pre)(old) && (self.post)(new) && (self.link)(old, new)
    }
}

/// The turn-evaluation context the reactive window reads — the Rust twin of the
/// executor's `EvalContext`, carrying the `height` the Lean `inWindow` gates on.
/// (The standalone crate does not link the executor's full `EvalContext`; this is
/// the minimal faithful carrier — the reactive layer reads only `height`.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvalContext {
    /// The turn height (the executor's `EvalContext::height` / `block_height`).
    pub height: u64,
}

impl EvalContext {
    /// A context at turn `height`.
    pub fn at_height(height: u64) -> Self {
        EvalContext { height }
    }
}

/// **`ReactiveAffordance`** — the deos element that reacts in THREE dimensions:
/// WHO (the cap-gate, in the carried [`CellAffordance`]), WHAT TRANSITION (the
/// [`TransitionGate`]), and WHEN (an inclusive height window
/// `[open_height, close_height]` over the turn height). The Rust twin of the Lean
/// `ReactiveAffordance`. The window is two-sided (a genuine `[open, close]` voting
/// window with an auto-closing deadline). The "vote" button is
/// `{ affordance: vote(requires ballot cap), gate: pending→pending ∧ tally+1,
/// open_height, close_height }`.
///
/// NOT new cryptography and NOT a new state machine: the cap-gate is the EXISTING
/// [`CellAffordance::authorized_for`] (`is_attenuation`, the proven lattice); a
/// committed fire rides the SAME [`AffordanceSurface::fire`] path (so the leg-4
/// attested-root binding is identical). What is NEW is the GATE SHAPE — the
/// relational `link` + the two-sided window, decidable conjunctions layered ON
/// TOP, never a new lattice.
pub struct ReactiveAffordance {
    /// The cap-gated effect-template (the REAL effect + its `required_rights`).
    pub affordance: CellAffordance,
    /// The transition gate (`pre`/`post`/`link`) the `(old, new)` must satisfy.
    pub gate: TransitionGate,
    /// The inclusive window OPEN height — the fire is refused before this height.
    pub open_height: u64,
    /// The inclusive window CLOSE height (the deadline) — the fire is refused
    /// after this height.
    pub close_height: u64,
}

impl std::fmt::Debug for ReactiveAffordance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReactiveAffordance")
            .field("affordance", &self.affordance)
            .field("gate", &self.gate)
            .field("open_height", &self.open_height)
            .field("close_height", &self.close_height)
            .finish()
    }
}

impl ReactiveAffordance {
    /// Assemble a reactive affordance: a cap-gated `affordance`, the transition
    /// `gate`, and the inclusive `[open_height, close_height]` window.
    pub fn new(
        affordance: CellAffordance,
        gate: TransitionGate,
        open_height: u64,
        close_height: u64,
    ) -> Self {
        ReactiveAffordance {
            affordance,
            gate,
            open_height,
            close_height,
        }
    }

    /// **`in_window(ctx)`** — the turn height lies in the inclusive window
    /// `[open_height, close_height]` (the Rust twin of the Lean `inWindow`).
    /// Before `open_height` the button has not yet opened; after `close_height` it
    /// has auto-closed (the deadline passed).
    pub fn in_window(&self, ctx: &EvalContext) -> bool {
        self.open_height <= ctx.height && ctx.height <= self.close_height
    }

    /// **`reactive_ok(held, ctx, old, new)`** — the THREE-WAY gate as one bool:
    /// the cap-gate AND the transition-gate AND the window-gate (the Rust twin of
    /// the Lean `reactiveOK`). THE predicate that says "this button may fire RIGHT
    /// NOW, for this viewer, on THIS transition, at THIS height". Drop ANY one
    /// gate and it is `false`.
    pub fn reactive_ok(
        &self,
        held: &SurfaceCapability,
        ctx: &EvalContext,
        old: &CellState,
        new: &CellState,
    ) -> bool {
        self.affordance.authorized_for(held)
            && self.gate.transition_ok(old, new)
            && self.in_window(ctx)
    }

    /// **`fire`** the reactive affordance for an actor holding `held`, at turn
    /// `ctx.height`, against the transition `(old, new)`. The Rust twin of the
    /// Lean `fireReactive` and the keystone `fireReactive_iff`: it commits — via
    /// the SAME [`AffordanceSurface::fire`] path, producing the genuine
    /// [`AffordanceIntent`] carrying the REAL effect — IFF ALL THREE gates pass:
    ///
    ///   1. the cap-gate ([`CellAffordance::authorized_for`] = `is_attenuation`),
    ///   2. THEN the transition-gate (`pre(old) && post(new) && link(old, new)`),
    ///   3. THEN the inclusive window (`open_height <= height <= close_height`).
    ///
    /// The refusal is precise and IN-BAND (never a silent run, never a forged
    /// surface):
    ///
    ///   * [`FireError::Unauthorized`] — the cap tooth (the actor lacks the
    ///     rights), the twin of `fireReactive_cap_fail_refuses`;
    ///   * [`FireError::TransitionUnmet`] — the transition tooth (this `old → new`
    ///     is not the one the button reacts to), the twin of
    ///     `fireReactive_transition_fail_refuses` /
    ///     `fireReactive_wrong_old_refuses` — a fully-authorized actor inside the
    ///     window is refused if the SAME `new` was reached from a `old` that
    ///     breaks the relational `link`;
    ///   * [`FireError::OutsideWindow`] — the deadline tooth (the height is
    ///     outside `[open, close]`), the twin of
    ///     `fireReactive_window_fail_refuses` / `fireReactive_after_deadline_refuses`.
    ///
    /// The gate order matches the Lean (`fireGate` then `transitionOK` then
    /// `inWindow`); the first failing gate names the refusal.
    pub fn fire(
        &self,
        actor: CellId,
        held: &SurfaceCapability,
        ctx: &EvalContext,
        old: &CellState,
        new: &CellState,
    ) -> Result<AffordanceIntent, FireError> {
        // (1) the cap tooth — the REAL `is_attenuation`, exactly as the
        //     non-reactive `AffordanceSurface::fire` runs it.
        if !self.affordance.authorized_for(held) {
            return Err(FireError::Unauthorized {
                affordance: self.affordance.name.clone(),
                required: self.affordance.required_rights.clone(),
            });
        }
        // (2) the transition tooth — `pre(old) && post(new) && link(old, new)`.
        //     A property of `new` alone is NOT enough: the `link` checks the
        //     SHAPE of the transition (the anti-"a good-looking new state is
        //     enough" pin).
        if !self.gate.transition_ok(old, new) {
            return Err(FireError::TransitionUnmet {
                affordance: self.affordance.name.clone(),
            });
        }
        // (3) the deadline tooth — the inclusive `[open, close]` window.
        if !self.in_window(ctx) {
            return Err(FireError::OutsideWindow {
                affordance: self.affordance.name.clone(),
                open: self.open_height,
                close: self.close_height,
                height: ctx.height,
            });
        }
        // All three gates passed: the SAME intent the non-reactive fire mints
        // (the leg-4 root-binding rides this exact path).
        Ok(AffordanceIntent {
            surface_cell: actor,
            affordance: self.affordance.name.clone(),
            actor,
            effect: self.affordance.effect_template.clone(),
        })
    }
}

/// **`Viewer`** — a membrane viewer (the Rust twin of the Lean `Viewer`): the
/// rights `held` (the cap dimension — the REAL `is_attenuation` gate input) PLUS a
/// `permits` predicate (the witness-graph projection — which affordance NAMES this
/// viewer's frustum authorizes them to SEE, a disclosure/clearance bit decided
/// OUTSIDE the fire-cap). Two viewers can share `held` but differ in `permits` —
/// the membrane divides them.
pub struct Viewer {
    /// The rights this viewer holds (the cap dimension).
    pub held: SurfaceCapability,
    /// The witness-graph projection: which affordance NAMES this viewer's frustum
    /// authorizes them to see (the disclosure dimension, independent of the
    /// fire-cap). The Lean keys on `Nat`; here affordance identity is the
    /// `String` name.
    pub permits: Box<dyn Fn(&str) -> bool>,
}

impl std::fmt::Debug for Viewer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Viewer")
            .field("held", &self.held)
            .field("permits", &"<Fn(&str) -> bool>")
            .finish()
    }
}

impl Viewer {
    /// A viewer holding `held` whose witness-graph projection is `permits`.
    pub fn new(held: SurfaceCapability, permits: Box<dyn Fn(&str) -> bool>) -> Self {
        Viewer { held, permits }
    }

    /// **`membrane_shows(aff)`** — the membrane projects affordance `aff` to this
    /// viewer IFF the viewer's caps authorize the fire
    /// (`aff.authorized_for(held)`, the REAL `is_attenuation`) AND the viewer's
    /// witness-graph permits the affordance's name (`permits(aff.name)`). The Rust
    /// twin of the Lean `membraneShows`: the per-viewer frustum surface as a
    /// conjunction of AUTHORITY and PROJECTION — the two dimensions the membrane
    /// negotiates.
    pub fn membrane_shows(&self, aff: &CellAffordance) -> bool {
        aff.authorized_for(&self.held) && (self.permits)(&aff.name)
    }

    /// **The read-cap weld** (`docs/deos/PRIVACY-CONFIDENTIALITY.md` §2c /
    /// Milestone 0 step 4): build a viewer whose `permits` disclosure bit is
    /// derived FROM read-cap possession, making the fog-of-war **cryptographic
    /// rather than advisory**.
    ///
    /// Today `permits` is a trusted local closure — a malicious surface could
    /// ignore it. Here the disclosure bit becomes "does the viewer hold a
    /// [`dregg_cell_crypto::ReadCap`] that derives the key for this affordance's slot?":
    /// `permits(name) = read_cap.derives(slot_of(name))`. The projection is then
    /// enforced by *not being able to decrypt* the underlying slot, not by a
    /// closure choosing to hide. This is the Lean `membraneShows` conjunct
    /// `readCapDerives(viewer.readcap, aff.slots)`.
    ///
    /// `slot_of` maps an affordance name to the cell slot whose read-cap entitlement
    /// gates its disclosure (the surface author declares this binding — e.g. a
    /// "view-balance" affordance maps to the balance slot). An affordance with no
    /// mapping is treated as **public** (no read-cap needed to see it), so this is
    /// strictly additive: affordances not tied to a confidential slot are shown
    /// exactly as before.
    ///
    /// The non-amplification proof extends for free: a reshared viewer cannot grant
    /// disclosure of a slot the resharer could not read, because the read-cap it
    /// hands cannot derive a key the resharer's `slots` did not entitle
    /// ([`dregg_cell_crypto::ReadCap::attenuate`] = `granted ⊆ held`).
    pub fn from_read_cap<F>(
        held: SurfaceCapability,
        read_cap: dregg_cell_crypto::ReadCap,
        slot_of: F,
    ) -> Self
    where
        F: Fn(&str) -> Option<usize> + 'static,
    {
        let permits = Box::new(move |name: &str| -> bool {
            match slot_of(name) {
                // The affordance is tied to a confidential slot: it is disclosed
                // IFF the held read-cap derives that slot's key (cryptographic).
                Some(slot) => read_cap.derives(slot),
                // No confidential slot: a public affordance, always disclosed.
                None => true,
            }
        });
        Viewer { held, permits }
    }
}

/// A stable, comparable readout of a [`dregg_turn::Effect`] template — its variant
/// tag + the principal cell(s) it acts on. (The `Effect` enum is not `PartialEq`
/// because some variants carry proofs / eventual refs; this is the
/// equality-friendly projection a test or a UI can compare.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectSummary {
    SetField {
        cell: CellId,
        index: usize,
    },
    Transfer {
        from: CellId,
        to: CellId,
        amount: u64,
    },
    GrantCapability {
        from: CellId,
        to: CellId,
    },
    RevokeCapability {
        cell: CellId,
        slot: u32,
    },
    EmitEvent {
        cell: CellId,
    },
    IncrementNonce {
        cell: CellId,
    },
    /// Any other real `Effect` variant, tagged by its name (still the genuine
    /// effect — only the *summary* is coarse).
    Other {
        tag: &'static str,
    },
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
        Effect::RefreshDelegation { .. } => "RefreshDelegation",
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
    /// The actor HOLDS the rights and the height is in the window, but the
    /// `old → new` TRANSITION is not the one this button reacts to (`pre(old)`,
    /// `post(new)`, or the relational `link(old, new)` failed) — the **transition
    /// tooth**, the twin of Lean `fireReactive_transition_fail_refuses` /
    /// `fireReactive_wrong_old_refuses`. The half a single-state cap-gate can never
    /// express: the SAME `new` reached from a `old` that breaks the `link` is
    /// REFUSED even with full caps, an open window, and a `new` satisfying `post`.
    /// The SHAPE of the transition is checked, not just the destination.
    TransitionUnmet {
        /// The affordance whose transition gate was not met.
        affordance: String,
    },
    /// The actor HOLDS the rights and the transition qualifies, but the turn
    /// `height` is OUTSIDE the inclusive `[open, close]` window — the **deadline
    /// tooth**, the twin of Lean `fireReactive_window_fail_refuses` /
    /// `fireReactive_after_deadline_refuses`. Past `close` (or before `open`) a
    /// fully-authorized, perfectly-qualifying transition auto-refuses: the surface
    /// reacts to the CLOCK, not just the state.
    OutsideWindow {
        /// The affordance whose window was missed.
        affordance: String,
        /// The window's inclusive OPEN height.
        open: u64,
        /// The window's inclusive CLOSE height (the deadline).
        close: u64,
        /// The turn height that fell outside `[open, close]`.
        height: u64,
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

    /// Convenience: project through a [`Membrane`] by its CAP dimension alone (the
    /// viewer's held authority is the membrane's [`Membrane::held`]). The
    /// [`Membrane`] carries only the cap ceiling, so this is the cap-only frustum;
    /// for the FULL per-viewer membrane — caps AND the witness-graph disclosure bit
    /// — use [`AffordanceSurface::project_membrane`] with a [`Viewer`].
    pub fn project_for_membrane(&self, membrane: &Membrane) -> Vec<CellAffordance> {
        self.project_for(membrane.held())
    }

    /// **The per-viewer MEMBRANE projection** — the disclosure-aware frustum, the
    /// Rust twin of the Lean `projectMembrane`. Return ONLY the affordances the
    /// `viewer`'s membrane SHOWS: those for which BOTH the cap-gate
    /// ([`CellAffordance::authorized_for`] = `is_attenuation`) AND the viewer's
    /// witness-graph projection ([`Viewer::permits`] on the affordance NAME) pass —
    /// i.e. [`Viewer::membrane_shows`].
    ///
    /// This is the fix to the cap-only [`AffordanceSurface::project_for`] /
    /// [`AffordanceSurface::project_for_membrane`] stub: those divide a surface by
    /// CAPS alone, so two viewers at EQUAL authority see the SAME set. The membrane
    /// divides BEYOND caps — two viewers with the SAME `held` but DIFFERENT
    /// `permits` get DISTINCT surfaces (the keystone `membrane_two_viewers_distinct`
    /// the cap-only stub refutes). The order is preserved (declaration order), so
    /// the projection is a stable sub-list.
    pub fn project_membrane(&self, viewer: &Viewer) -> Vec<CellAffordance> {
        self.affordances
            .iter()
            .filter(|a| viewer.membrane_shows(a))
            .cloned()
            .collect()
    }

    /// The names a `viewer` is shown through the MEMBRANE (sorted) — the
    /// per-viewer, disclosure-aware affordance set, the thing two
    /// EQUAL-authority-but-different-`permits` viewers DIVERGE on (the cap-only
    /// [`AffordanceSurface::visible_names`] cannot tell them apart).
    pub fn membrane_names(&self, viewer: &Viewer) -> Vec<String> {
        let mut names: Vec<String> = self
            .project_membrane(viewer)
            .into_iter()
            .map(|a| a.name)
            .collect();
        names.sort();
        names
    }

    /// The names a viewer is authorized to see (sorted) — the per-viewer affordance
    /// set, the thing two different-cap viewers DIVERGE on.
    pub fn visible_names(&self, held: &SurfaceCapability) -> Vec<String> {
        let mut names: Vec<String> = self.project_for(held).into_iter().map(|a| a.name).collect();
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

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
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
            EffectSummary::SetField {
                cell: doc,
                index: 3
            }
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
            vec![
                "comment".to_string(),
                "edit".to_string(),
                "view".to_string()
            ]
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
            assert!(
                proj.iter().any(|a| a.name == name),
                "{name} must be visible to editor"
            );
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
        assert_eq!(
            intent.effect_summary(),
            EffectSummary::EmitEvent { cell: doc }
        );
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
            EffectSummary::GrantCapability {
                from: doc,
                to: cid(99)
            }
        );
    }

    #[test]
    fn firing_a_missing_affordance_is_no_such_affordance() {
        let surface = doc_surface(cid(6));
        assert_eq!(
            surface
                .fire("nonexistent", cid(50), &admin_held())
                .unwrap_err(),
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
        let (_web, surface, snapshot) =
            snapshot_of_doc(10, AuthRequired::None, InteractionLog::new(), false);
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
        let (web, surface, snapshot) = snapshot_of_doc(11, AuthRequired::None, log, false);

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
            vec![
                "comment".to_string(),
                "edit".to_string(),
                "view".to_string()
            ]
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
        let (web1, surface1, snap1) = snapshot_of_doc(12, AuthRequired::None, confined, false);
        let (_aff, live1) =
            rehydrate_affordances(&snap1, &surface1, &Membrane::new(admin_held()), &web1)
                .expect("rehydrates");
        assert_eq!(live1, Rehydration::ReplayedDeterministic);
        assert!(live1.is_faithful());

        // Leaky: one ambient interaction → ReconstructedApproximate.
        let mut leaky = InteractionLog::new();
        leaky.record_attested_fetch(DreggUri::new(cid(62)), witness);
        leaky.record_ambient("raw fetch outside the membrane");
        let (web2, surface2, snap2) = snapshot_of_doc(13, AuthRequired::None, leaky, false);
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
            matches!(
                result,
                Err(AffordanceRehydrateError::Rehydrate(RehydrateError::Fetch(
                    _
                )))
            ),
            "an unattested scene must yield NO interactive surface even with full caps"
        );
    }

    #[test]
    fn rehydrating_against_the_wrong_surface_is_a_boundary_mismatch() {
        // You cannot rehydrate a snapshot against a DIFFERENT surface than its
        // frustum bounded — the boundary cell cross-check refuses it.
        let (web, _surface, snapshot) =
            snapshot_of_doc(15, AuthRequired::None, InteractionLog::new(), false);
        let other_surface = doc_surface(cid(81)); // a different cell
        let result = rehydrate_affordances(
            &snapshot,
            &other_surface,
            &Membrane::new(admin_held()),
            &web,
        );
        assert_eq!(
            result.unwrap_err(),
            AffordanceRehydrateError::BoundaryMismatch
        );
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
            EffectSummary::SetField {
                cell: doc,
                index: 1
            }
        );
        assert_eq!(
            surface.get("admin").unwrap().effect_summary(),
            EffectSummary::GrantCapability {
                from: doc,
                to: cid(99)
            }
        );
        // And each is matchable as the genuine enum (not a parallel stub type).
        assert!(matches!(
            surface.get("edit").unwrap().effect_template,
            Effect::SetField { .. }
        ));
        assert!(matches!(
            surface.get("admin").unwrap().effect_template,
            Effect::GrantCapability { .. }
        ));
    }

    #[test]
    fn declare_replaces_by_name() {
        // A re-declared affordance (same name) replaces the prior one — names are
        // unique within a surface.
        let doc = cid(91);
        let surface = AffordanceSurface::new(doc)
            .declare(CellAffordance::new(
                "x",
                AuthRequired::None,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "x",
                AuthRequired::Signature,
                set_field(doc, 0),
            ));
        assert_eq!(surface.affordances.len(), 1);
        // The SECOND declaration won.
        assert_eq!(
            surface.get("x").unwrap().required_rights,
            AuthRequired::Signature
        );
        assert_eq!(
            surface.get("x").unwrap().effect_summary(),
            EffectSummary::SetField {
                cell: doc,
                index: 0
            }
        );
    }

    // ════════════════════════════════════════════════════════════════════════
    // The TEMPORAL / TRANSITION rung — the Rust mirror of the Lean
    // `Dregg2.Deos.Reactive` §4/§6/§7 teeth (both polarities, the vote/resolve
    // worked example from the Lean §8 `#guard`s).
    // ════════════════════════════════════════════════════════════════════════

    use dregg_cell::state::CellState;

    /// A field-element from a small u64 (big-endian last 8 bytes) — matches the
    /// cell crate's `field_to_u64` lift and the `app-framework` sibling lane.
    fn fe(n: u64) -> [u8; 32] {
        let mut b = [0u8; 32];
        b[24..32].copy_from_slice(&n.to_be_bytes());
        b
    }

    const STATUS_SLOT: usize = 0;
    const TALLY_SLOT: usize = 1;
    const PENDING: u64 = 1;
    const RESOLVED: u64 = 2;
    const QUORUM: u64 = 3;

    /// A council-cell state with the given status + tally (the `old`/`new` records
    /// the transition gate reads BOTH of).
    fn council(status: u64, tally: u64) -> CellState {
        let mut s = CellState::new(0);
        s.set_field(STATUS_SLOT, fe(status));
        s.set_field(TALLY_SLOT, fe(tally));
        s
    }

    /// Read a u64 slot off a `CellState` (the Rust twin of the Lean
    /// `Value.scalar`) — `None` if absent. Used by the relational `link`s.
    fn slot_u64(s: &CellState, slot: usize) -> Option<u64> {
        s.get_field(slot).map(|f| {
            let mut last8 = [0u8; 8];
            last8.copy_from_slice(&f[24..32]);
            u64::from_be_bytes(last8)
        })
    }

    /// A predicate "status slot == `want`".
    fn status_is(want: u64) -> RecordPredicate {
        Box::new(move |s: &CellState| slot_u64(s, STATUS_SLOT) == Some(want))
    }

    /// The VOTE gate: PENDING → PENDING AND the tally went up by EXACTLY ONE (a
    /// ballot added) — the relational `link` reading BOTH records (the half a
    /// single-state gate cannot witness).
    fn vote_gate() -> TransitionGate {
        TransitionGate::new(
            status_is(PENDING),
            status_is(PENDING),
            Box::new(|old: &CellState, new: &CellState| {
                match (slot_u64(old, TALLY_SLOT), slot_u64(new, TALLY_SLOT)) {
                    (Some(a), Some(b)) => b == a + 1,
                    _ => false,
                }
            }),
        )
    }

    /// The RESOLVE gate: PENDING → RESOLVED AND the tally CROSSED quorum on this
    /// transition (`old < QUORUM <= new`) — the crossing, not the level.
    fn resolve_gate() -> TransitionGate {
        TransitionGate::new(
            status_is(PENDING),
            status_is(RESOLVED),
            Box::new(|old: &CellState, new: &CellState| {
                match (slot_u64(old, TALLY_SLOT), slot_u64(new, TALLY_SLOT)) {
                    (Some(a), Some(b)) => a < QUORUM && QUORUM <= b,
                    _ => false,
                }
            }),
        )
    }

    /// The "vote" reactive button: the ballot cap (`Either`) AND the add-a-ballot
    /// transition AND inside `[10, 20]`.
    fn vote_btn(cell: CellId) -> ReactiveAffordance {
        ReactiveAffordance::new(
            CellAffordance::new("vote", AuthRequired::Either, set_field(cell, TALLY_SLOT)),
            vote_gate(),
            10,
            20,
        )
    }

    /// The "resolve" reactive button: the chair cap (root / `None`) AND the
    /// quorum-crossing transition AND inside `[10, 30]`.
    fn resolve_btn(cell: CellId) -> ReactiveAffordance {
        ReactiveAffordance::new(
            CellAffordance::new("resolve", AuthRequired::None, set_field(cell, STATUS_SLOT)),
            resolve_gate(),
            10,
            30,
        )
    }

    // member holds Either (the ballot cap); chair holds None (root); observer
    // holds Signature (neither).
    fn member_held() -> SurfaceCapability {
        SurfaceCapability::root(cid(20), AuthRequired::Either)
    }
    fn chair_held() -> SurfaceCapability {
        SurfaceCapability::root(cid(21), AuthRequired::None)
    }
    fn observer_held() -> SurfaceCapability {
        SurfaceCapability::root(cid(22), AuthRequired::Signature)
    }

    #[test]
    fn reactive_all_three_gates_pass_fires_carrying_the_real_effect() {
        // The POSITIVE corner (twin of `fireReactive_all_pass` +
        // `fireReactive_carries_real_effect`): member, ballot-added (tally 0→1),
        // PENDING→PENDING, inside the window ⇒ FIRES with the REAL effect.
        let doc = cid(30);
        let btn = vote_btn(doc);
        let ctx = EvalContext::at_height(15);
        let intent = btn
            .fire(
                cid(50),
                &member_held(),
                &ctx,
                &council(PENDING, 0),
                &council(PENDING, 1),
            )
            .expect("the qualifying transition inside the window fires");
        assert_eq!(intent.actor, cid(50));
        assert_eq!(intent.affordance, "vote");
        // The committed fire carries the REAL effect (the leg-4 binding rides the
        // SAME path) — a genuine SetField, not a stub.
        assert_eq!(
            intent.effect_summary(),
            EffectSummary::SetField {
                cell: doc,
                index: TALLY_SLOT
            }
        );
        assert!(matches!(intent.effect, Effect::SetField { .. }));
    }

    #[test]
    fn reactive_transition_tooth_wrong_old_refuses() {
        // THE TRANSITION TOOTH (twin of `fireReactive_wrong_old_refuses`): the
        // SAME `new` (PENDING, a valid tally) reached from a WRONG `old` that
        // breaks the relational `link` REFUSES — EVEN with full caps, an open
        // window, and a `new` satisfying `post`. A single-state gate would PASS
        // (the destination looks fine); the SHAPE of the transition is checked.
        let doc = cid(31);
        let btn = vote_btn(doc);
        let ctx = EvalContext::at_height(15); // inside [10, 20]

        // (a) NO ballot added (tally 1→1): the link `new == old + 1` fails.
        let refused = btn.fire(
            cid(50),
            &member_held(),
            &ctx,
            &council(PENDING, 1),
            &council(PENDING, 1),
        );
        assert_eq!(
            refused.unwrap_err(),
            FireError::TransitionUnmet {
                affordance: "vote".to_string()
            }
        );

        // (b) ballot jumped by TWO (tally 0→2): same `new`-status, wrong shape.
        assert_eq!(
            btn.fire(
                cid(50),
                &member_held(),
                &ctx,
                &council(PENDING, 0),
                &council(PENDING, 2)
            )
            .unwrap_err(),
            FireError::TransitionUnmet {
                affordance: "vote".to_string()
            }
        );

        // CONTRAST: the SAME `new` (PENDING, tally 1) from the RIGHT `old`
        // (tally 0) FIRES — so the refusal above is SOLELY the broken link, not
        // the destination.
        assert!(btn
            .fire(
                cid(50),
                &member_held(),
                &ctx,
                &council(PENDING, 0),
                &council(PENDING, 1)
            )
            .is_ok());
    }

    #[test]
    fn reactive_deadline_tooth_outside_window_refuses_both_sides() {
        // THE DEADLINE TOOTH (twin of `fireReactive_after_deadline_refuses` +
        // `fireReactive_window_fail_refuses`): a fully-authorized,
        // perfectly-qualifying transition is REFUSED past `close` (and before
        // `open`). The surface reacts to the CLOCK.
        let doc = cid(32);
        let btn = vote_btn(doc); // window [10, 20]
        let old = council(PENDING, 0);
        let new = council(PENDING, 1); // a perfect add-a-ballot transition

        // After the deadline (height 25 > close 20) ⇒ OutsideWindow.
        let after = btn.fire(
            cid(50),
            &member_held(),
            &EvalContext::at_height(25),
            &old,
            &new,
        );
        assert_eq!(
            after.unwrap_err(),
            FireError::OutsideWindow {
                affordance: "vote".to_string(),
                open: 10,
                close: 20,
                height: 25,
            }
        );

        // Before it opens (height 5 < open 10) ⇒ OutsideWindow too.
        assert_eq!(
            btn.fire(
                cid(50),
                &member_held(),
                &EvalContext::at_height(5),
                &old,
                &new
            )
            .unwrap_err(),
            FireError::OutsideWindow {
                affordance: "vote".to_string(),
                open: 10,
                close: 20,
                height: 5,
            }
        );
    }

    #[test]
    fn reactive_temporal_htmx_tooth_same_move_lit_inside_dark_outside() {
        // THE TEMPORAL HTMX TOOTH (twin of `fireReactive_window_reactive`): the
        // SAME member's SAME ballot is LIT at height 15 (inside) and DARK at 25
        // (after) — the verdict decided by TIME, holding the move fixed.
        let doc = cid(33);
        let btn = vote_btn(doc);
        let old = council(PENDING, 0);
        let new = council(PENDING, 1);

        assert!(btn
            .fire(
                cid(50),
                &member_held(),
                &EvalContext::at_height(15),
                &old,
                &new
            )
            .is_ok());
        assert!(btn
            .fire(
                cid(50),
                &member_held(),
                &EvalContext::at_height(25),
                &old,
                &new
            )
            .is_err());
    }

    #[test]
    fn reactive_cap_tooth_only_the_ballot_holder_may_vote() {
        // THE CAP TOOTH (twin of `fireReactive_cap_fail_refuses`): an observer (no
        // ballot cap) is REFUSED on a perfect transition inside the window — the
        // cap-gate is the REAL `is_attenuation`, checked FIRST.
        let doc = cid(34);
        let btn = vote_btn(doc);
        let refused = btn.fire(
            cid(50),
            &observer_held(),
            &EvalContext::at_height(15),
            &council(PENDING, 0),
            &council(PENDING, 1),
        );
        assert!(matches!(
            refused.unwrap_err(),
            FireError::Unauthorized { affordance, .. } if affordance == "vote"
        ));
    }

    #[test]
    fn reactive_resolve_fires_only_on_the_quorum_crossing_transition() {
        // RESOLVE fires ONLY on the quorum-REACHED transition (the §8 resolve
        // corners): chair, tally 2→3 crossing quorum, PENDING→RESOLVED, inside the
        // window ⇒ FIRES; a non-crossing (already ≥ quorum) REFUSES; a member
        // (no chair cap) cannot resolve even on the crossing.
        let doc = cid(35);
        let btn = resolve_btn(doc); // window [10, 30]
        let ctx = EvalContext::at_height(22);

        // (✓) chair, quorum crossed (2→3), PENDING→RESOLVED ⇒ FIRES.
        assert!(btn
            .fire(
                cid(60),
                &chair_held(),
                &ctx,
                &council(PENDING, 2),
                &council(RESOLVED, 3)
            )
            .is_ok());

        // (✗) chair, but the link fails (old already ≥ quorum: 3→3, no crossing).
        assert_eq!(
            btn.fire(
                cid(60),
                &chair_held(),
                &ctx,
                &council(PENDING, 3),
                &council(RESOLVED, 3)
            )
            .unwrap_err(),
            FireError::TransitionUnmet {
                affordance: "resolve".to_string()
            }
        );

        // (✗) member (no root cap) cannot resolve even on the crossing ⇒ cap tooth.
        assert!(matches!(
            btn.fire(
                cid(61),
                &member_held(),
                &ctx,
                &council(PENDING, 2),
                &council(RESOLVED, 3)
            ),
            Err(FireError::Unauthorized { .. })
        ));
    }

    #[test]
    fn reactive_ok_agrees_with_fire_on_every_corner() {
        // `reactive_ok` is the three-way conjunction `fire` gates on (twin of
        // `fireReactive_iff` / `reactiveOK_iff`): it is `true` EXACTLY when `fire`
        // commits. Cross-check the predicate against the verb on each corner.
        let doc = cid(36);
        let btn = vote_btn(doc);
        let good_old = council(PENDING, 0);
        let good_new = council(PENDING, 1);
        let bad_new = council(PENDING, 2); // breaks the +1 link

        let cases = [
            (member_held(), 15, &good_old, &good_new, true), // all pass
            (member_held(), 15, &good_old, &bad_new, false), // transition fails
            (member_held(), 25, &good_old, &good_new, false), // window fails
            (observer_held(), 15, &good_old, &good_new, false), // cap fails
        ];
        for (held, h, old, new, want) in cases {
            let ctx = EvalContext::at_height(h);
            assert_eq!(btn.reactive_ok(&held, &ctx, old, new), want);
            // the verb agrees with the predicate, both polarities.
            assert_eq!(btn.fire(cid(50), &held, &ctx, old, new).is_ok(), want);
        }
    }

    // ── The MEMBRANE keystone: two viewers at EQUAL authority, DIFFERENT
    //    witness-graph projection, see DISTINCT surfaces. ──

    /// A secret-ballot "view tally" affordance anyone with `Signature` may fire —
    /// IF their frustum permits it.
    fn tally_view(doc: CellId) -> CellAffordance {
        CellAffordance::new("tally", AuthRequired::Signature, emit_event(doc))
    }

    #[test]
    fn membrane_two_viewers_at_equal_authority_see_distinct_surfaces() {
        // THE MEMBRANE KEYSTONE (twin of `membrane_two_viewers_distinct`): two
        // viewers with the SAME caps (both `Signature`, both clear the cap-gate)
        // but DIFFERENT `permits` — one frustum SHOWS the tally, the other does
        // NOT — get DISTINCT surfaces. The membrane divides BEYOND caps. This is
        // the keystone the cap-only `project_for` stub REFUTES (it would show both
        // the SAME set).
        let doc = cid(37);
        let aff = tally_view(doc);
        let surface = AffordanceSurface::new(doc).declare(tally_view(doc));

        let trustee = Viewer::new(
            SurfaceCapability::root(cid(40), AuthRequired::Signature),
            Box::new(|name: &str| name == "tally"),
        );
        let guest = Viewer::new(
            SurfaceCapability::root(cid(41), AuthRequired::Signature),
            Box::new(|_| false),
        );

        // EQUAL authority: both viewers' caps authorize the fire (the cap-only
        // gate cannot tell them apart).
        assert!(aff.authorized_for(&trustee.held));
        assert!(aff.authorized_for(&guest.held));
        assert_eq!(
            aff.authorized_for(&trustee.held),
            aff.authorized_for(&guest.held)
        );

        // … yet the membrane DIVIDES them: the trustee's frustum SHOWS it, the
        // guest's does NOT.
        assert!(trustee.membrane_shows(&aff));
        assert!(!guest.membrane_shows(&aff));

        // The projection bears it out: the trustee sees the tally button, the
        // guest sees NOTHING — distinct surfaces over the SAME cap-authority.
        assert_eq!(surface.membrane_names(&trustee), vec!["tally".to_string()]);
        assert!(surface.membrane_names(&guest).is_empty());
        assert_ne!(
            surface.membrane_names(&trustee),
            surface.membrane_names(&guest)
        );
    }

    #[test]
    fn membrane_still_respects_the_cap_dimension() {
        // The membrane is a CONJUNCTION: a viewer whose `permits` says yes but
        // whose CAPS fall short still sees nothing (the cap dimension survives the
        // second dimension). An observer at `Signature` permitting an `admin`
        // (req `None` / root) affordance is NOT shown it.
        let doc = cid(38);
        let admin = CellAffordance::new("admin", AuthRequired::None, grant_cap(doc, cid(99)));
        let surface = AffordanceSurface::new(doc).declare(CellAffordance::new(
            "admin",
            AuthRequired::None,
            grant_cap(doc, cid(99)),
        ));

        // permits EVERYTHING, but holds only Signature (lacks root).
        let eager_but_weak = Viewer::new(
            SurfaceCapability::root(cid(42), AuthRequired::Signature),
            Box::new(|_| true),
        );
        assert!(!admin.authorized_for(&eager_but_weak.held)); // cap-gate fails
        assert!(!eager_but_weak.membrane_shows(&admin)); // so the membrane hides it
        assert!(surface.membrane_names(&eager_but_weak).is_empty());

        // The root holder permitting it IS shown it (both dimensions pass).
        let root_trustee = Viewer::new(
            SurfaceCapability::root(cid(43), AuthRequired::None),
            Box::new(|name: &str| name == "admin"),
        );
        assert!(root_trustee.membrane_shows(&admin));
        assert_eq!(
            surface.membrane_names(&root_trustee),
            vec!["admin".to_string()]
        );
    }

    /// THE READ-CAP MEMBRANE WELD (`docs/deos/PRIVACY-CONFIDENTIALITY.md` §2c):
    /// the disclosure bit is derived FROM read-cap possession, so two viewers at
    /// EQUAL write-authority but DIFFERENT read-caps see distinct surfaces — and
    /// the divider is *cryptographic* (the narrow cap cannot derive the slot key),
    /// not a trusted closure. The Rust face of the non-vacuity tooth at the
    /// membrane layer.
    #[test]
    fn membrane_disclosure_is_welded_to_read_cap_possession() {
        use dregg_cell_crypto::{FieldSet, ReadCap, ViewKey};

        let doc = cid(50);
        // Two confidential affordances, each tied to a cell slot whose read-cap
        // entitlement gates its disclosure: "view-salary" → slot 5,
        // "view-notes" → slot 3.
        let salary = CellAffordance::new("view-salary", AuthRequired::Signature, emit_event(doc));
        let notes = CellAffordance::new("view-notes", AuthRequired::Signature, emit_event(doc));
        let surface = AffordanceSurface::new(doc)
            .declare(CellAffordance::new(
                "view-salary",
                AuthRequired::Signature,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "view-notes",
                AuthRequired::Signature,
                emit_event(doc),
            ));

        // The surface author's name→slot binding.
        let slot_of = |name: &str| -> Option<usize> {
            match name {
                "view-salary" => Some(5),
                "view-notes" => Some(3),
                _ => None,
            }
        };

        let view_key = ViewKey::from_root([0x5A; 32]);
        // A WIDE read-cap over slots {3,5}; a NARROW one (attenuated) over {3}.
        let wide_cap = ReadCap::new(doc, FieldSet::from_slots(&[3, 5]), view_key);
        let narrow_cap = wide_cap
            .attenuate(FieldSet::single(3))
            .expect("attenuation");

        // Two viewers at EQUAL write-authority (both Signature), differing ONLY in
        // their read-cap — the membrane permits-bit comes from the cap.
        let wide_viewer = Viewer::from_read_cap(
            SurfaceCapability::root(cid(60), AuthRequired::Signature),
            wide_cap,
            slot_of,
        );
        let narrow_viewer = Viewer::from_read_cap(
            SurfaceCapability::root(cid(61), AuthRequired::Signature),
            narrow_cap,
            slot_of,
        );

        // EQUAL cap-authority: the cap-gate cannot tell them apart.
        assert!(salary.authorized_for(&wide_viewer.held));
        assert!(salary.authorized_for(&narrow_viewer.held));

        // … yet the read-cap DIVIDES them cryptographically:
        // BOTH see "view-notes" (slot 3, which both caps derive).
        assert!(wide_viewer.membrane_shows(&notes));
        assert!(narrow_viewer.membrane_shows(&notes));
        // ONLY the wide viewer sees "view-salary" (slot 5 — the narrow cap cannot
        // derive that slot's key, so the fog-of-war hides it).
        assert!(wide_viewer.membrane_shows(&salary));
        assert!(!narrow_viewer.membrane_shows(&salary));

        // The projection bears it out — distinct surfaces over equal write-auth.
        assert_eq!(
            surface.membrane_names(&wide_viewer),
            vec!["view-notes".to_string(), "view-salary".to_string()]
        );
        assert_eq!(
            surface.membrane_names(&narrow_viewer),
            vec!["view-notes".to_string()]
        );
        assert_ne!(
            surface.membrane_names(&wide_viewer),
            surface.membrane_names(&narrow_viewer)
        );
    }
}
