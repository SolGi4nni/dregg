//! Frustum-snapshots + the cap-membrane — **the dregg-only novelty**, brought
//! into the framework's own bones over its REAL `is_attenuation` lattice.
//!
//! `docs/deos/DEOS.md` (§"the frustum-culled snapshot"): a deos "screenshot" is a
//! frame of the certified compositor over the witness-graph; it embeds a
//! **sturdyref behind a membrane**, so *opening the image* re-attaches a live,
//! **per-viewer, attenuated, liveness-typed** interactive surface. A normal
//! screenshot is a dead pixel grid; a deos snapshot is *a paused camera on a
//! witnessed scene that re-expands inside its own jail.* This requires the verified
//! witness-graph (the frame is faithful by construction) + the ocap substrate (the
//! rehydration is confined by construction) + the sturdyref/membrane (the right is
//! revocable + per-viewer).
//!
//! ## Re-expression, not a feature-port
//!
//! The standalone `starbridge-web-surface` crate prototyped this shape over
//! `dregg_firmament` surface caps. THIS module re-expresses it over the
//! framework's OWN primitives — [`dregg_cell::AuthRequired`] +
//! [`dregg_cell::is_attenuation`] + the [`crate::affordance::AffordanceSurface`] —
//! so the snapshot/rehydrate capability composes with the affordance surface a deos
//! app already declares, with no new trust and no dependency on the standalone
//! crate. The three load-bearing moves are identical:
//!
//! 1. **The membrane is the sole minter of a per-viewer projection** and it
//!    composes the REAL [`is_attenuation`] across hops — a reshare A→B→C can NEVER
//!    amplify ([`Membrane::reshare`] re-applies the gate, [`RehydrateError::Amplification`]
//!    on any overstep). This is `DEOS.md`'s "membrane non-amplification" theorem,
//!    realized.
//! 2. **The frustum-snapshot is TINY** — a [`Sturdyref`] (the lineage authority +
//!    the witness-log) + the culling boundary, NOT the affordance data. Re-expanding
//!    it ([`Sturdyref::rehydrate_for`]) re-derives the per-viewer affordance set
//!    through the membrane, so a snapshot a powerful holder took yields a NARROWER
//!    surface to a weaker viewer — the screenshot respects the lattice.
//! 3. **The liveness-type is DERIVED** from the source context's witness-log, never
//!    assigned by hand ([`Rehydration::classify`]): `Live` if the sources are still
//!    reachable, else `ReplayedDeterministic` iff every interaction was a witnessed
//!    turn, else `ReconstructedApproximate`. `DEOS.md`'s "rehydration confinement =
//!    the liveness-type" — the system cannot lie about which kind of true you get.

use dregg_cell::{AuthRequired, is_attenuation};
use dregg_types::CellId;

use crate::affordance::{AffordanceSurface, CellAffordance};

// =============================================================================
// Rehydration — the DERIVED liveness-type
// =============================================================================

/// The **liveness-type** a rehydration yields — which *kind of true* the reacquired
/// surface is. DERIVED from the source context's confinement, never assigned.
///
/// The ordering is "more true / more confined" → "less": `Live` >
/// `ReplayedDeterministic` > `ReconstructedApproximate`. The [`Ord`] derive follows
/// that order (a lower variant is a weaker guarantee), so a membrane that must
/// DOWNGRADE on a chained reacquisition takes the `min` ([`Rehydration::min`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rehydration {
    /// The least-true / least-confined: at least one ambient interaction was never
    /// witnessed, so the non-determinism that shaped the scene was never captured.
    /// (Lowest, so `min` picks it.)
    ReconstructedApproximate,
    /// Every external interaction was an attested turn in the witness-graph — the
    /// confined fragment, faithful replay by construction.
    ReplayedDeterministic,
    /// The source contexts are still reachable — the live scene.
    Live,
}

impl Rehydration {
    /// **DERIVE** the liveness-type from a context's interaction log + whether its
    /// source contexts are still reachable. The value is COMPUTED from the
    /// witness-graph slice, never assigned by hand:
    ///
    /// - `Live` iff `sources_reachable` (the live scene is still there to reconnect to);
    /// - else `ReplayedDeterministic` iff EVERY interaction in `log` is witnessed (an
    ///   attested turn — the confined fragment);
    /// - else `ReconstructedApproximate` (some interaction was ambient/un-witnessed).
    ///
    /// An **empty** log replays deterministically: a context that did nothing
    /// external has no un-witnessed behaviour to reconstruct (vacuously confined).
    pub fn classify(log: &InteractionLog, sources_reachable: bool) -> Rehydration {
        if sources_reachable {
            return Rehydration::Live;
        }
        if log.all_witnessed() {
            Rehydration::ReplayedDeterministic
        } else {
            Rehydration::ReconstructedApproximate
        }
    }

    /// The weaker (more-reconstructed) of two liveness-types — what a chained
    /// reacquisition takes (a reshare is at most as live as its weakest hop).
    pub fn min(self, other: Rehydration) -> Rehydration {
        std::cmp::min(self, other)
    }

    /// Is this rehydration faithful-by-construction (live OR the confined replay)?
    /// `false` only for [`Rehydration::ReconstructedApproximate`] — the honest
    /// "this is a reconstruction" signal a viewer must heed.
    pub fn is_faithful(&self) -> bool {
        !matches!(self, Rehydration::ReconstructedApproximate)
    }

    /// A one-line badge the shell renders, so the liveness-type is *visible* on every
    /// reacquisition (`DEOS.md`: the system cannot lie about which kind of true you get).
    pub fn badge(&self) -> &'static str {
        match self {
            Rehydration::Live => "LIVE (reconnected to the running scene)",
            Rehydration::ReplayedDeterministic => {
                "REPLAYED-DETERMINISTIC (every interaction was an attested turn — confined)"
            }
            Rehydration::ReconstructedApproximate => {
                "RECONSTRUCTED-APPROXIMATE (touched ambient state — faithful, not the same)"
            }
        }
    }
}

/// One external interaction the source context made, tagged **witnessed** (it went
/// through a verified turn — its receipt is in the witness-graph) vs. **ambient**
/// (it reached outside the membrane — a raw read, an un-witnessed agent choice).
///
/// In the framework, a witnessed interaction is one whose `turn_hash` is a real
/// (non-zero) executed-turn receipt — the same `TurnReceipt::turn_hash` the embedded
/// executor returns for an affordance fire. "Witnessed" is therefore not a bare
/// boolean: an interaction is witnessed iff it carries a genuine turn hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Interaction {
    /// A witnessed turn — its non-determinism is captured in the witness-graph.
    /// Carries the `turn_hash` of the executed turn (a real receipt's hash); its
    /// presence (non-zero) is what makes the interaction witnessed.
    WitnessedTurn {
        /// The cell the turn acted on (the surface whose affordance was fired).
        surface: CellId,
        /// The executed turn's hash (a real `TurnReceipt::turn_hash`). A zeroed hash
        /// is treated as un-witnessed (no real turn captured the non-determinism).
        turn_hash: [u8; 32],
    },
    /// A raw, un-witnessed external interaction (an ambient read, an out-of-band
    /// agent choice). NOTHING in the witness-graph captured the non-determinism it
    /// introduced — any context that made one can only be reconstructed.
    Ambient {
        /// A human-readable note for diagnostics. Not load-bearing — the *variant* is
        /// what classifies.
        what: String,
    },
}

impl Interaction {
    /// A witnessed interaction — a turn on `surface` whose receipt carries
    /// `turn_hash`.
    pub fn witnessed_turn(surface: CellId, turn_hash: [u8; 32]) -> Interaction {
        Interaction::WitnessedTurn { surface, turn_hash }
    }

    /// An ambient interaction — reached outside the membrane, never witnessed.
    pub fn ambient(what: impl Into<String>) -> Interaction {
        Interaction::Ambient { what: what.into() }
    }

    /// Was this interaction witnessed (a real executed turn in the graph)?
    ///
    /// A [`Interaction::WitnessedTurn`] is witnessed iff its `turn_hash` is non-zero
    /// (a genuine receipt). A purported witnessed turn carrying a zeroed hash did NOT
    /// capture any non-determinism — it classifies as ambient would. This is the
    /// anti-toy hinge: "witnessed" is derived from a real turn hash, not asserted.
    pub fn is_witnessed(&self) -> bool {
        match self {
            Interaction::WitnessedTurn { turn_hash, .. } => *turn_hash != [0u8; 32],
            Interaction::Ambient { .. } => false,
        }
    }
}

/// The source context's external-interaction log — the input the liveness-type is
/// DERIVED from (the witness-graph's per-context slice).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InteractionLog {
    interactions: Vec<Interaction>,
}

impl InteractionLog {
    /// An empty log (a context that has made no external interaction yet —
    /// vacuously confined).
    pub fn new() -> Self {
        InteractionLog {
            interactions: Vec::new(),
        }
    }

    /// Record an interaction (builder-style). The graph notes whether it was
    /// witnessed.
    pub fn record(mut self, interaction: Interaction) -> Self {
        self.interactions.push(interaction);
        self
    }

    /// True iff EVERY recorded interaction was witnessed (an attested turn) — the
    /// confined fragment. Vacuously true for an empty log.
    pub fn all_witnessed(&self) -> bool {
        self.interactions.iter().all(Interaction::is_witnessed)
    }

    /// The number of recorded interactions.
    pub fn len(&self) -> usize {
        self.interactions.len()
    }

    /// True if no interactions were recorded.
    pub fn is_empty(&self) -> bool {
        self.interactions.is_empty()
    }
}

// =============================================================================
// The cap-membrane — the enforcer
// =============================================================================

/// What can go wrong rehydrating a [`Sturdyref`] through a [`Membrane`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RehydrateError {
    /// The membrane refused: the viewer's authority and the sturdyref's lineage are
    /// INCOMPARABLE under [`is_attenuation`] (neither attenuates the other), so there
    /// is no projection both admit. The anti-ghost tooth — a reshare can never
    /// overstep the lattice. (This is the fog-of-war "incomparable identities cannot
    /// peek" refusal: two distinct `Custom { vk_hash }` identities, or `Signature` vs
    /// `Proof`, have no common projection.)
    Amplification {
        /// The authority the viewer held.
        held: AuthRequired,
        /// The lineage the sturdyref was a projection of.
        lineage: AuthRequired,
    },
}

impl std::fmt::Display for RehydrateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RehydrateError::Amplification { held, lineage } => write!(
                f,
                "rehydration refused: held {held:?} and lineage {lineage:?} are incomparable \
                 (no projection both admit)"
            ),
        }
    }
}

impl std::error::Error for RehydrateError {}

/// The **meet** of two authorities under the REAL [`is_attenuation`] lattice — the
/// narrower authority both admit, or `None` if they are incomparable.
///
/// `meet(a, b)` is:
/// - `a` if `a` is an attenuation of `b` (`a ⊆ b`) — `a` is the narrower;
/// - `b` if `b` is an attenuation of `a` (`b ⊆ a`);
/// - `None` if NEITHER attenuates the other (incomparable: distinct `Custom`,
///   `Signature` vs `Proof`) — there is no common projection.
///
/// This is the load-bearing lattice operation the membrane composes: it can never
/// return an authority wider than EITHER input, so a projection minted from it never
/// amplifies. Returning `None` is the structural refusal.
pub fn meet_authority(a: &AuthRequired, b: &AuthRequired) -> Option<AuthRequired> {
    if is_attenuation(b, a) {
        // a ⊆ b: a is the narrower.
        Some(a.clone())
    } else if is_attenuation(a, b) {
        // b ⊆ a: b is the narrower.
        Some(b.clone())
    } else {
        None
    }
}

/// The cap-**membrane** — the enforcer + the sole minter of a per-viewer projection.
///
/// It wraps a viewer's **held authority** (what THIS viewer is entitled to at most).
/// At rehydration it derives the projection as the meet of (held) ∧ (the sturdyref's
/// lineage) through the GENUINE [`is_attenuation`], so a projection can never exceed
/// either the held authority OR the lineage. Resharing (A→B→C) threads a NEW membrane
/// whose held authority is the prior hop's projection; [`Membrane::reshare`]
/// re-applies the meet, refusing (`Amplification`) any hop that would overstep.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Membrane {
    /// The authority THIS viewer holds — the ceiling on any projection minted
    /// through this membrane.
    held: AuthRequired,
}

impl Membrane {
    /// Construct a membrane for a viewer holding `held` authority. Any projection
    /// minted through it is `≤ held` (and `≤` the sturdyref's lineage).
    pub fn new(held: AuthRequired) -> Self {
        Membrane { held }
    }

    /// The authority this membrane's viewer holds (read-only).
    pub fn held(&self) -> &AuthRequired {
        &self.held
    }

    /// Re-derive the per-viewer **projection authority**: `(held) ∧ (lineage)` through
    /// the REAL attenuation lattice ([`meet_authority`]).
    ///
    /// Returns the narrower authority both the viewer and the lineage admit, or
    /// [`RehydrateError::Amplification`] iff they are incomparable (no projection both
    /// admit — the structural refusal). Anti-amplification holds by construction: the
    /// result is an [`is_attenuation`] of BOTH inputs.
    pub fn project_authority(
        &self,
        lineage: &AuthRequired,
    ) -> Result<AuthRequired, RehydrateError> {
        meet_authority(&self.held, lineage).ok_or_else(|| RehydrateError::Amplification {
            held: self.held.clone(),
            lineage: lineage.clone(),
        })
    }

    /// **Reshare** A→B→C: thread a NEW membrane for a downstream viewer holding
    /// `downstream_held`, whose ceiling is the meet of THIS membrane's held authority
    /// and the downstream viewer's — so the chain is monotone non-amplifying. Refused
    /// (`Amplification`) if the two are incomparable.
    ///
    /// This is the chained-attenuation algebra: `C's authority ⊆ B's held ⊆ A's`. It
    /// is the same [`is_attenuation`] lattice composed across hops.
    pub fn reshare(&self, downstream_held: &AuthRequired) -> Result<Membrane, RehydrateError> {
        let chained = self.project_authority(downstream_held)?;
        Ok(Membrane::new(chained))
    }
}

// =============================================================================
// Sturdyref + the frustum-snapshot
// =============================================================================

/// A persistable **sturdyref** into a deos surface — the bearer cap a frustum-snapshot
/// embeds behind the membrane.
///
/// It is TINY: it carries the **lineage authority** (the surface authority the
/// snapshot was a certified projection of — the membrane re-derives every viewer's
/// projection as an attenuation of this, never wider), the backing `cell`, and the
/// source context's [`InteractionLog`] (the witness-graph slice the liveness-type is
/// DERIVED from) — NOT the affordance data. The affordances are re-expanded
/// per-viewer at rehydration from the live [`AffordanceSurface`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sturdyref {
    /// The cell the snapshot is a camera on (the surface being re-viewed).
    pub cell: CellId,
    /// The publisher's authority lineage: the surface authority the snapshot was a
    /// certified projection of. Every viewer's projection is an attenuation of this.
    pub lineage: AuthRequired,
    /// The witness-graph slice for the source context (its external-interaction log).
    /// The liveness-type is DERIVED from this at reacquisition.
    pub witness_log: InteractionLog,
    /// Are the source contexts still reachable? (Set by whoever holds the live
    /// scene.) A snapshot handed to someone cold after the session ended carries
    /// `false`.
    pub sources_reachable: bool,
}

impl Sturdyref {
    /// Construct a sturdyref over `cell` with the publisher's `lineage`, the
    /// source-context `witness_log`, and whether the sources are still reachable.
    pub fn new(
        cell: CellId,
        lineage: AuthRequired,
        witness_log: InteractionLog,
        sources_reachable: bool,
    ) -> Self {
        Sturdyref {
            cell,
            lineage,
            witness_log,
            sources_reachable,
        }
    }

    /// The liveness-type this sturdyref would rehydrate as, DERIVED from its
    /// witness-log + source reachability — independent of any viewer's caps (the
    /// liveness-type is a property of the *source context's confinement*, not of who
    /// is looking).
    pub fn liveness(&self) -> Rehydration {
        Rehydration::classify(&self.witness_log, self.sources_reachable)
    }

    /// **Rehydrate** this snapshot for a viewer through their [`Membrane`], against
    /// the live `surface` — re-expanding the per-viewer slice.
    ///
    /// 1. The membrane derives the projection authority `(viewer held) ∧ (lineage)`
    ///    through the REAL [`is_attenuation`] — `Amplification` if incomparable.
    /// 2. The affordances the viewer reacquires are exactly the live surface's
    ///    affordances that the *projection authority* admits ([`AffordanceSurface::project_for`])
    ///    — so a snapshot a powerful holder took yields a NARROWER affordance set to a
    ///    weaker viewer. The screenshot respects the lattice.
    /// 3. The liveness-type is the snapshot's DERIVED [`Sturdyref::liveness`].
    ///
    /// Returns the per-viewer [`RehydratedSurface`].
    pub fn rehydrate_for(
        &self,
        membrane: &Membrane,
        surface: &AffordanceSurface,
    ) -> Result<RehydratedSurface, RehydrateError> {
        let projection = membrane.project_authority(&self.lineage)?;
        let affordances = surface.project_for(&projection);
        Ok(RehydratedSurface {
            cell: self.cell,
            projection,
            affordances,
            liveness: self.liveness(),
        })
    }
}

/// The per-viewer **rehydrated surface** a snapshot re-expands into — the affordance
/// slice the viewer's projection authorizes + the DERIVED liveness-type.
///
/// `DEOS.md`: two agents opening "the same" snapshot do not rehydrate identical
/// instantiations — each re-derives, across the membrane, the slice their
/// capabilities authorize. Different viewers get DIFFERENT `affordances` over the
/// SAME sturdyref.
#[derive(Clone, Debug)]
pub struct RehydratedSurface {
    /// The cell the rehydration re-attached to.
    pub cell: CellId,
    /// The per-viewer projection authority — the negotiated `(held) ∧ (lineage)`
    /// meet. The ceiling on what this viewer can fire.
    pub projection: AuthRequired,
    /// The affordances this viewer reacquired — the live surface's affordances the
    /// projection authority admits. A NARROWER set for a weaker viewer.
    pub affordances: Vec<CellAffordance>,
    /// The liveness-type — which kind of true this rehydration is (DERIVED, never
    /// assigned).
    pub liveness: Rehydration,
}

impl RehydratedSurface {
    /// The names of the affordances this viewer reacquired (sorted) — the per-viewer
    /// surface the two viewers DIVERGE on.
    pub fn visible_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.affordances.iter().map(|a| a.name.clone()).collect();
        names.sort();
        names
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_turn::action::{Effect, Event};

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn emit_event(cell: CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: Event {
                topic: [1u8; 32],
                data: vec![],
            },
        }
    }

    /// The canonical doc surface: view@Signature, comment@Either, admin@None.
    fn doc_surface(doc: CellId) -> AffordanceSurface {
        AffordanceSurface::named(doc, "doc")
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "comment",
                AuthRequired::Either,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None,
                emit_event(doc),
            ))
    }

    // ── the meet under the REAL lattice ──

    #[test]
    fn meet_is_the_narrower_when_comparable() {
        // Either ⊃ Signature ⇒ meet is Signature (the narrower).
        assert_eq!(
            meet_authority(&AuthRequired::Either, &AuthRequired::Signature),
            Some(AuthRequired::Signature)
        );
        assert_eq!(
            meet_authority(&AuthRequired::Signature, &AuthRequired::Either),
            Some(AuthRequired::Signature)
        );
        // None ⊃ everything ⇒ meet(None, X) = X.
        assert_eq!(
            meet_authority(&AuthRequired::None, &AuthRequired::Either),
            Some(AuthRequired::Either)
        );
        // Equal ⇒ itself.
        assert_eq!(
            meet_authority(&AuthRequired::Signature, &AuthRequired::Signature),
            Some(AuthRequired::Signature)
        );
    }

    #[test]
    fn meet_is_none_when_incomparable() {
        // Signature vs Proof: incomparable (neither attenuates the other).
        assert_eq!(
            meet_authority(&AuthRequired::Signature, &AuthRequired::Proof),
            None
        );
        // Two distinct Custom identities: incomparable — THE fog-of-war refusal.
        let red = AuthRequired::Custom { vk_hash: [1u8; 32] };
        let blue = AuthRequired::Custom { vk_hash: [2u8; 32] };
        assert_eq!(meet_authority(&red, &blue), None);
        // The same Custom identity: comparable (meet is itself).
        assert_eq!(meet_authority(&red, &red.clone()), Some(red));
    }

    // ── the membrane: project + reshare are non-amplifying ──

    #[test]
    fn membrane_projects_the_meet_and_refuses_incomparable() {
        // A viewer holding Either, a lineage of Signature ⇒ projection Signature.
        let membrane = Membrane::new(AuthRequired::Either);
        assert_eq!(
            membrane
                .project_authority(&AuthRequired::Signature)
                .unwrap(),
            AuthRequired::Signature
        );
        // A viewer holding Signature, a lineage of Proof ⇒ incomparable ⇒ refused.
        let sig_viewer = Membrane::new(AuthRequired::Signature);
        assert_eq!(
            sig_viewer.project_authority(&AuthRequired::Proof),
            Err(RehydrateError::Amplification {
                held: AuthRequired::Signature,
                lineage: AuthRequired::Proof,
            })
        );
    }

    #[test]
    fn reshare_chains_attenuation_never_amplifies() {
        // A (None/root) → B (Either) → C (Signature): each hop narrows.
        let a = Membrane::new(AuthRequired::None);
        let b = a.reshare(&AuthRequired::Either).unwrap();
        assert_eq!(*b.held(), AuthRequired::Either);
        let c = b.reshare(&AuthRequired::Signature).unwrap();
        assert_eq!(*c.held(), AuthRequired::Signature);
        // C's authority ⊆ B's held ⊆ A's — the chained lattice law.
        assert!(is_attenuation(b.held(), c.held()));
        assert!(is_attenuation(a.held(), b.held()));
        // A reshare to an INCOMPARABLE authority is refused.
        assert!(matches!(
            c.reshare(&AuthRequired::Proof),
            Err(RehydrateError::Amplification { .. })
        ));
    }

    // ── the frustum-snapshot: re-expands per-viewer, respects the lattice ──

    #[test]
    fn a_snapshot_rehydrates_narrower_for_a_weaker_viewer() {
        let doc = cid(1);
        let surface = doc_surface(doc);
        // A root holder snapshots the surface (lineage None — the full surface).
        let snap = Sturdyref::new(doc, AuthRequired::None, InteractionLog::new(), false);

        // The root holder rehydrates the FULL surface.
        let root = Membrane::new(AuthRequired::None);
        let root_view = snap.rehydrate_for(&root, &surface).unwrap();
        assert_eq!(
            root_view.visible_names(),
            vec![
                "admin".to_string(),
                "comment".to_string(),
                "view".to_string()
            ]
        );

        // A viewer (Signature) rehydrating the SAME snapshot reacquires only {view} —
        // the screenshot respects the lattice; it cannot leak the admin affordance.
        let viewer = Membrane::new(AuthRequired::Signature);
        let viewer_view = snap.rehydrate_for(&viewer, &surface).unwrap();
        assert_eq!(viewer_view.visible_names(), vec!["view".to_string()]);

        // DIVERGENCE over the SAME sturdyref — the per-viewer property.
        assert_ne!(root_view.visible_names(), viewer_view.visible_names());
    }

    #[test]
    fn rehydration_refuses_an_incomparable_viewer() {
        let doc = cid(2);
        let surface = doc_surface(doc);
        // A snapshot whose lineage is a Custom identity (e.g. a fog-of-war side).
        let red = AuthRequired::Custom { vk_hash: [7u8; 32] };
        let snap = Sturdyref::new(doc, red, InteractionLog::new(), true);
        // A DIFFERENT-identity viewer cannot rehydrate it at all — the membrane mints
        // NO projection (the fog-of-war "cannot peek" refusal).
        let blue = Membrane::new(AuthRequired::Custom { vk_hash: [9u8; 32] });
        assert!(matches!(
            snap.rehydrate_for(&blue, &surface),
            Err(RehydrateError::Amplification { .. })
        ));
    }

    // ── the liveness-type is DERIVED from the witness-log ──

    #[test]
    fn liveness_is_derived_live_when_reachable() {
        let snap = Sturdyref::new(cid(3), AuthRequired::None, InteractionLog::new(), true);
        assert_eq!(snap.liveness(), Rehydration::Live);
        assert!(snap.liveness().is_faithful());
    }

    #[test]
    fn liveness_is_replayed_deterministic_when_all_witnessed() {
        // Sources gone, but every interaction was a witnessed turn (non-zero hash) ⇒
        // the confined fragment.
        let log = InteractionLog::new()
            .record(Interaction::witnessed_turn(cid(4), [3u8; 32]))
            .record(Interaction::witnessed_turn(cid(4), [5u8; 32]));
        let snap = Sturdyref::new(cid(4), AuthRequired::None, log, false);
        assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
        assert!(snap.liveness().is_faithful());
    }

    #[test]
    fn liveness_is_reconstructed_when_an_interaction_was_ambient() {
        // One ambient interaction (or a zeroed turn hash) ⇒ reconstruction.
        let log = InteractionLog::new()
            .record(Interaction::witnessed_turn(cid(5), [3u8; 32]))
            .record(Interaction::ambient("read wall-clock"));
        let snap = Sturdyref::new(cid(5), AuthRequired::None, log, false);
        assert_eq!(snap.liveness(), Rehydration::ReconstructedApproximate);
        assert!(!snap.liveness().is_faithful());

        // A WitnessedTurn with a ZEROED hash is NOT witnessed — anti-toy.
        let fake = InteractionLog::new().record(Interaction::witnessed_turn(cid(5), [0u8; 32]));
        assert!(!fake.all_witnessed());
    }

    #[test]
    fn liveness_min_takes_the_weaker_for_a_chain() {
        assert_eq!(
            Rehydration::Live.min(Rehydration::ReplayedDeterministic),
            Rehydration::ReplayedDeterministic
        );
        assert_eq!(
            Rehydration::ReplayedDeterministic.min(Rehydration::ReconstructedApproximate),
            Rehydration::ReconstructedApproximate
        );
    }
}
