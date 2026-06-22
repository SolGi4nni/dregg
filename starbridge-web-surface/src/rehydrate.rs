//! Rehydratable surfaces — the sturdyref-behind-a-membrane, the per-viewer
//! projection, and the `Rehydration` liveness-type as a **confinement readout**.
//!
//! `docs/desktop-os-research/REHYDRATABLE-SURFACES.md`, made into steel. The doc's
//! thesis: a dregg "screenshot" is the present render-output of a certified
//! compositor over a witness-graph; what it actually embeds is a **sturdyref behind
//! a membrane**; "opening" it is the **membrane-negotiated, per-viewer
//! reacquisition** of the witnessed state it was always a certified projection of.
//! This module ships the three load-bearing pieces, each on the REAL dregg cap +
//! attestation primitives the rest of the crate already names — never a parallel
//! model:
//!
//! 1. [`Rehydration`] — the liveness-type, **DERIVED** from a context's
//!    interaction log ([`Rehydration::classify`]), not hand-assigned. A context is
//!    [`Rehydration::ReplayedDeterministic`] *iff* every external interaction it
//!    made was an **attested turn** captured in the witness-graph (a `dregg://`
//!    attested fetch / a receipt in the stream);
//!    [`Rehydration::ReconstructedApproximate`] *iff* it touched any
//!    un-witnessed/ambient interaction; [`Rehydration::Live`] *iff* the source
//!    contexts are still reachable. This lands the doc's
//!    "derived-from-attested-non-determinism (TARGET)" row: the enum does double
//!    duty as an honesty label AND a readout of how much behaviour stayed inside
//!    the capability discipline. `ReplayedDeterministic == "everything this context
//!    did went through the membrane."`
//!
//! 2. [`Membrane`] — the cap-membrane (the enforcer). It wraps a held cap-set and
//!    (a) re-derives the per-viewer [`Projection`] = (held authority) ∧ (the
//!    graph's permitted projections), and (b) **composes attenuation across
//!    reacquisition hops** (A→B→C) using the REAL [`dregg_cell::is_attenuation`]
//!    (`granted ⊆ held`) at each hop. A reshare that tries to AMPLIFY (C receives
//!    more authority than B actually held) is REFUSED — the anti-ghost tooth.
//!
//! 3. [`Sturdyref`] + [`rehydrate`] — a persistable cap-handle into the
//!    witness-graph (the crate's existing `dregg://` + [`AttestedRoot`] machinery)
//!    and the membrane-negotiated reacquisition returning the per-viewer projection
//!    + its liveness-type. The fetch is the existing
//!    [`crate::web_of_cells::WebOfCells`] attested-fetch path: fetch = verified turn
//!    returning attested content.
//!
//! ## What is real vs. the seam
//!
//! - **Real (the cap discipline + attestation + the derivation):** the membrane
//!   composes the GENUINE `is_attenuation` per hop (the proven lattice); the
//!   liveness-type is COMPUTED from witnessed-vs-ambient interactions, never a
//!   hand-set field; the fetch is the real `dregg://` attested cross-cell read; the
//!   projection is a real [`SurfaceCapability`] (a firmament `Capability`).
//! - **The seams (named, not papered):** the certified compositor-PD (the
//!   framebuffer/input cap holder, `ARCHITECTURES.md`) and the libservo link are
//!   still wood — a `dregg://` fetch stands in for the compositor's render-pass over
//!   the witness-graph, exactly as `MockSurface` stands in for the libservo
//!   `WebView`. The chained-attenuation algebra IS pinned here (it is the same
//!   `is_attenuation` lattice the cap crown proves, lifted to projection
//!   composition — the doc's residual #1).

use dregg_cell::{is_attenuation, AuthRequired};
use dregg_types::AttestedRoot;

use crate::delegate::{PermissionKind, SurfaceCapability};
use crate::web_of_cells::{AttestedResource, DreggUri, FetchError, OriginChrome, WebOfCells};

use std::collections::BTreeSet;

/// The liveness-type the membrane carries on every reacquisition — and a
/// **confinement readout**, not just an honesty label.
///
/// `REHYDRATABLE-SURFACES.md` "the liveness cost is a TYPE": *open the image* must
/// tell you *which kind of true* you are getting, by construction. The system
/// cannot lie about whether you are touching the live scene or a faithful replay
/// because the reacquisition is typed — and (residual #3, the TARGET landed here)
/// the type is **derived from how much of the source context's behaviour stayed
/// inside the capability membrane**:
///
/// - [`Rehydration::Live`] — the source contexts are still reachable; you reconnect
///   to the running scene.
/// - [`Rehydration::ReplayedDeterministic`] — the source contexts are gone, but
///   EVERY external interaction the context made was an **attested turn captured in
///   the witness-graph** (a `dregg://` attested fetch / a receipt in the stream).
///   The non-determinism was witnessed, so replay is faithful-by-construction.
///   This variant == "everything this context did went through the membrane" — the
///   *exactly confined* fragment.
/// - [`Rehydration::ReconstructedApproximate`] — the context touched at least one
///   **un-witnessed/ambient** interaction (a raw fetch, an un-witnessed
///   timing/agent choice). The thing that made it non-deterministic was never
///   witnessed, so what you reacquire is a reconstruction, not a resurrection.
///
/// The ordering is "more true / more confined" → "less": `Live` >
/// `ReplayedDeterministic` > `ReconstructedApproximate`. The
/// [`PartialOrd`]/[`Ord`] derive follows that order (a lower variant is a weaker
/// guarantee), so a membrane that must DOWNGRADE on a chained reacquisition takes
/// the `min`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rehydration {
    /// The least-true / least-confined: at least one ambient interaction was never
    /// witnessed. (Lowest, so `min` picks it.)
    ReconstructedApproximate,
    /// Every external interaction was an attested turn in the witness-graph — the
    /// confined fragment, faithful replay by construction.
    ReplayedDeterministic,
    /// The source contexts are still reachable — the live scene.
    Live,
}

impl Rehydration {
    /// **DERIVE** the liveness-type from a context's interaction log + whether its
    /// source contexts are still reachable. This is the load-bearing move: the
    /// value is COMPUTED from the witness-graph, never assigned by hand.
    ///
    /// - `Live` iff `sources_reachable` (the live scene is still there to reconnect
    ///   to);
    /// - else `ReplayedDeterministic` iff EVERY interaction in `log` is
    ///   [`Interaction::is_witnessed`] (every external interaction was an attested
    ///   turn captured in the graph — the confined fragment);
    /// - else `ReconstructedApproximate` (some interaction was ambient/un-witnessed,
    ///   so the non-determinism that shaped it was never captured).
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

    /// Is this rehydration faithful-by-construction (live OR the confined replay)?
    /// `false` only for [`Rehydration::ReconstructedApproximate`] — the honest
    /// "this is a reconstruction" signal a viewer must heed.
    pub fn is_faithful(&self) -> bool {
        !matches!(self, Rehydration::ReconstructedApproximate)
    }

    /// A one-line badge the shell renders alongside the trusted-path chrome, so the
    /// liveness-type is *visible* on every reacquisition (the doc's "the system
    /// cannot lie about which kind of true you are getting").
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

/// One external interaction a servo context made, tagged **witnessed** (it went
/// through the membrane — a `dregg://` attested fetch / a receipt in the stream) vs.
/// **ambient** (it reached outside the membrane — a raw fetch, an un-witnessed
/// timing or agent choice).
///
/// `REHYDRATABLE-SURFACES.md` residual #3: "a servo context whose external
/// interactions are themselves `dregg://` attested fetches (cap-gated,
/// receipt-logged) has its non-determinism captured in the witness-graph as
/// attested turns → `ReplayedDeterministic` by construction; a context that reached
/// outside the membrane … is intrinsically `ReconstructedApproximate`, because the
/// thing that made it non-deterministic was never witnessed."
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Interaction {
    /// A `dregg://` attested fetch (or any receipt-logged turn) — the
    /// non-determinism is captured in the witness-graph. Carries the
    /// [`AttestedRoot`] that witnesses it, so "witnessed" is not a bare boolean but
    /// a real attestation the membrane could re-verify.
    AttestedFetch {
        /// The cell the fetch resolved (the origin of the witnessed turn).
        origin: DreggUri,
        /// The genuine federation attestation binding the turn into the
        /// witness-graph. Its presence is what makes the interaction *witnessed*.
        witness: AttestedRoot,
    },
    /// A raw, un-witnessed external interaction (a non-`dregg://` fetch, an ambient
    /// timer read, an out-of-band agent choice). NOTHING in the witness-graph
    /// captured the non-determinism this introduced — so any context that made one
    /// can only ever be reconstructed, not replayed deterministically.
    Ambient {
        /// A human-readable note for the demo/diagnostics (e.g. "raw fetch
        /// https://ad.example.com", "read wall-clock"). Not load-bearing — the
        /// *variant* is what classifies.
        what: String,
    },
}

impl Interaction {
    /// A witnessed interaction — a `dregg://` attested fetch carrying the real
    /// federation attestation that captures its non-determinism in the graph.
    pub fn attested_fetch(origin: DreggUri, witness: AttestedRoot) -> Interaction {
        Interaction::AttestedFetch { origin, witness }
    }

    /// An ambient interaction — reached outside the membrane, never witnessed.
    pub fn ambient(what: impl Into<String>) -> Interaction {
        Interaction::Ambient { what: what.into() }
    }

    /// Was this interaction witnessed (an attested turn in the graph)?
    ///
    /// For an [`Interaction::AttestedFetch`] this is not a bare tag: the witness is
    /// only honoured if the carried [`AttestedRoot`] actually binds the receipt
    /// stream (`is_v4_receipt_complete`) AND carries a quorum (`has_quorum`). A
    /// purported "attested" fetch whose attestation does not even structurally hold
    /// is NOT witnessed — it cannot have captured the non-determinism — so it
    /// classifies as ambient would. This is the anti-toy hinge: "witnessed" is
    /// derived from a real attestation, not asserted.
    pub fn is_witnessed(&self) -> bool {
        match self {
            Interaction::AttestedFetch { witness, .. } => {
                witness.is_v4_receipt_complete() && witness.has_quorum()
            }
            Interaction::Ambient { .. } => false,
        }
    }
}

/// A servo context's external-interaction log — the input the liveness-type is
/// DERIVED from.
///
/// `REHYDRATABLE-SURFACES.md`: replay-fidelity is bounded by how deterministically
/// the witness-graph captured the servo non-determinism. This is that graph's
/// per-context slice: the ordered list of external interactions, each
/// witnessed-or-ambient. [`Rehydration::classify`] reads it.
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

    /// Record an interaction (the context reached out; the graph notes whether it
    /// went through the membrane).
    pub fn record(&mut self, interaction: Interaction) -> &mut Self {
        self.interactions.push(interaction);
        self
    }

    /// Convenience: record a witnessed `dregg://` attested fetch.
    pub fn record_attested_fetch(&mut self, origin: DreggUri, witness: AttestedRoot) -> &mut Self {
        self.record(Interaction::attested_fetch(origin, witness))
    }

    /// Convenience: record an ambient (un-witnessed) interaction.
    pub fn record_ambient(&mut self, what: impl Into<String>) -> &mut Self {
        self.record(Interaction::ambient(what))
    }

    /// Did EVERY interaction go through the membrane (was witnessed)? The predicate
    /// that separates `ReplayedDeterministic` from `ReconstructedApproximate`. An
    /// empty log is vacuously all-witnessed.
    pub fn all_witnessed(&self) -> bool {
        self.interactions.iter().all(Interaction::is_witnessed)
    }

    /// The count of ambient (un-witnessed) interactions — the number of places the
    /// context escaped the membrane. Zero == fully confined. (A scalar confinement
    /// readout for diagnostics; `all_witnessed() == (ambient_count() == 0)`.)
    pub fn ambient_count(&self) -> usize {
        self.interactions
            .iter()
            .filter(|i| !i.is_witnessed())
            .count()
    }

    /// The total number of recorded interactions.
    pub fn len(&self) -> usize {
        self.interactions.len()
    }

    /// Is the log empty?
    pub fn is_empty(&self) -> bool {
        self.interactions.is_empty()
    }

    /// The recorded interactions (read-only).
    pub fn interactions(&self) -> &[Interaction] {
        &self.interactions
    }
}

/// A **sturdyref** — a persistable, serializable cap-handle into the
/// witness-graph, the thing actually embedded in the "screenshot".
///
/// `REHYDRATABLE-SURFACES.md` "crystal vs cursor was a false binary": the artifact
/// is neither a self-contained offline crystal nor a mere live cursor that dies
/// with the contexts. It is a sturdyref — handed to someone cold, it *re-establishes*
/// a live connection on activation. "The unit of portability was never the data or
/// the connection — it is the revocable right to renegotiate the connection."
///
/// Concretely this reuses the crate's existing `dregg://` machinery: the sturdyref
/// names the origin cell via a [`DreggUri`] (the bearer cap into a specific cell)
/// and carries the **publisher's authority lineage** — the [`SurfaceCapability`]
/// the published surface was a certified projection of. The membrane re-derives a
/// per-viewer projection as an attenuation of THAT lineage; a viewer never gets the
/// publisher's full authority, only `(their held) ∧ (the lineage)`.
///
/// It also carries the source context's [`InteractionLog`] (the witness-graph slice
/// the frame was a projection of) so the liveness-type can be DERIVED at
/// reacquisition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sturdyref {
    /// The `dregg://` ref into the origin cell — the persistable bearer cap.
    pub uri: DreggUri,
    /// The publisher's authority lineage: the surface authority the published
    /// frame was a certified projection of. The membrane re-derives every viewer's
    /// projection as an attenuation of this — never wider.
    pub lineage: SurfaceCapability,
    /// The witness-graph slice for the source context (its external-interaction
    /// log). The liveness-type is DERIVED from this at reacquisition.
    pub witness_log: InteractionLog,
    /// Are the source contexts still reachable? (Set by whoever holds the live
    /// scene; drives the `Live` vs replay/reconstruct branch.) A frame handed to
    /// someone cold after the session ended carries `false`.
    pub sources_reachable: bool,
}

impl Sturdyref {
    /// Construct a sturdyref over `uri` with the publisher's `lineage`, the
    /// source-context `witness_log`, and whether the sources are still reachable.
    pub fn new(
        uri: DreggUri,
        lineage: SurfaceCapability,
        witness_log: InteractionLog,
        sources_reachable: bool,
    ) -> Self {
        Sturdyref {
            uri,
            lineage,
            witness_log,
            sources_reachable,
        }
    }

    /// The liveness-type this sturdyref would rehydrate as, DERIVED from its
    /// witness-log + source reachability — independent of any viewer's caps (the
    /// liveness-type is a property of the *source context's confinement*, not of
    /// who is looking). [`rehydrate`] returns exactly this alongside the per-viewer
    /// projection.
    pub fn liveness(&self) -> Rehydration {
        Rehydration::classify(&self.witness_log, self.sources_reachable)
    }
}

/// The per-viewer **projection** a rehydration yields — the slice of the surface a
/// given viewer's caps authorize, plus the liveness-type and the trusted-path
/// chrome.
///
/// `REHYDRATABLE-SURFACES.md` "the membrane makes rehydration relational, not
/// absolute": two agents opening "the same" screenshot do not rehydrate identical
/// instantiations — each negotiates, across the membrane, the slice their
/// capabilities authorize. The frustum is re-derived per-viewer at the membrane
/// from (their authority) ∧ (the graph's permitted projections).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Projection {
    /// The per-viewer surface authority: the negotiated `(held) ∧ (lineage)`
    /// attenuation. A genuine [`SurfaceCapability`] (a firmament `Capability`), so
    /// the projection IS a real cap — not a parallel handle. Different viewers get
    /// different projections of the SAME sturdyref.
    pub surface: SurfaceCapability,
    /// The attested content the `dregg://` fetch returned (the rehydrated bytes +
    /// the attestation chain the viewer verifies BEFORE rendering).
    pub resource: AttestedResource,
    /// The trusted-path origin chrome, drawn from the LEDGER (the cell id +
    /// committed URL + rights lineage + finality) — never the fetched content.
    pub chrome: OriginChrome,
    /// The liveness-type, DERIVED from the source context's witness-log — which
    /// kind of true this rehydration is.
    pub liveness: Rehydration,
}

/// What can go wrong rehydrating a sturdyref through a membrane.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RehydrateError {
    /// The membrane refused: the viewer's requested projection would AMPLIFY beyond
    /// what the lineage (or a prior hop) actually held — `is_attenuation` rejected
    /// it. The anti-ghost tooth: a reshare can never overstep the lattice.
    Amplification,
    /// The `dregg://` fetch failed (dead link, tampered content, forged
    /// attestation, no quorum) — the underlying attested cross-cell read rejected.
    Fetch(FetchError),
}

impl From<FetchError> for RehydrateError {
    fn from(e: FetchError) -> Self {
        RehydrateError::Fetch(e)
    }
}

/// The cap-**membrane** — the enforcer. It wraps a viewer's held cap-set and a
/// (possibly chained) attenuation lineage, and is the sole place a per-viewer
/// projection is minted.
///
/// `REHYDRATABLE-SURFACES.md` "the membrane makes rehydration relational": the
/// membrane is where "I shared a screenshot" stops being "I leaked my session" and
/// becomes "I extended a revocable, attenuated, per-viewer right to re-view". It
/// (a) re-checks authority at reacquisition, (b) attenuates what is exposed, and
/// (c) **composes attenuation across chained reacquisitions** (A→B→C) — residual #1,
/// "the chained-attenuation algebra … is the same `is_attenuation` lattice the cap
/// crown already proves, lifted to projection composition."
///
/// The membrane holds a viewer's **held authority** (what THIS viewer is entitled
/// to at most). At rehydration it derives the projection as the meet of (held) ∧
/// (the sturdyref's lineage); the meet is computed through the GENUINE
/// [`dregg_cell::is_attenuation`] per hop, so a projection can never exceed either
/// the held authority OR the lineage. Resharing (A→B→C) threads a NEW membrane
/// whose held authority is a strict attenuation of the prior hop's projection;
/// [`Membrane::reshare`] re-applies `is_attenuation`, refusing any hop that would
/// amplify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Membrane {
    /// The authority THIS viewer holds — the ceiling on any projection minted
    /// through this membrane. A genuine [`SurfaceCapability`].
    held: SurfaceCapability,
}

impl Membrane {
    /// Construct a membrane for a viewer holding `held` authority. The projection
    /// minted through it is always `≤ held` (and `≤` the sturdyref's lineage).
    pub fn new(held: SurfaceCapability) -> Self {
        Membrane { held }
    }

    /// The authority this membrane's viewer holds (read-only).
    pub fn held(&self) -> &SurfaceCapability {
        &self.held
    }

    /// Re-derive the per-viewer **projection frustum**: `(held authority) ∧ (the
    /// graph's permitted projections)`, where the graph's permitted projections are
    /// the sturdyref's `lineage`.
    ///
    /// This is the meet of two surface authorities through the REAL attenuation
    /// lattice. The result holds, for each axis:
    ///
    /// - **window rights:** the `is_attenuation`-meet of `held.window.rights` and
    ///   `lineage.window.rights` — the *narrower* of the two (and if they are
    ///   incomparable, the projection is refused, because there is no common
    ///   authority both sides admit);
    /// - **fetch/navigate allowlists:** the set intersection (a viewer can only
    ///   reach origins BOTH its held caps and the lineage permit — `wildcard ∩ X =
    ///   X`);
    /// - **permissions:** the set intersection.
    ///
    /// The minted surface is bound to the sturdyref's origin cell (the thing being
    /// re-viewed). Returns [`RehydrateError::Amplification`] iff the two window
    /// rights are incomparable (no projection both admit) — the structural refusal.
    ///
    /// Anti-amplification holds by construction: the result's rights are
    /// `is_attenuation` of BOTH inputs, and the result's sets are subsets of BOTH
    /// inputs' sets, so the projection can never exceed either the held authority or
    /// the lineage.
    pub fn project(
        &self,
        lineage: &SurfaceCapability,
    ) -> Result<SurfaceCapability, RehydrateError> {
        // (1) Window rights: the meet under the REAL lattice. The narrower of the
        //     two is the one that is an attenuation of the other; if neither
        //     attenuates the other they are incomparable and there is no projection
        //     both admit.
        let rights = meet_rights(&self.held.window.rights, &lineage.window.rights)
            .ok_or(RehydrateError::Amplification)?;
        // (2) Fetch / navigate allowlists: the intersection (reach BOTH permit).
        let fetch_allow = intersect_allow(&self.held.fetch_allow, &lineage.fetch_allow);
        let navigate_allow = intersect_allow(&self.held.navigate_allow, &lineage.navigate_allow);
        // (3) Permissions: the intersection (carry only what BOTH hold).
        let permissions: BTreeSet<PermissionKind> = self
            .held
            .permissions
            .intersection(&lineage.permissions)
            .copied()
            .collect();

        // The projection is bound to the origin cell being re-viewed (the
        // lineage's cell), carrying the meet authority. It IS a firmament cap.
        let cell = lineage.cell().or_else(|| self.held.cell());
        let surface = match cell {
            Some(cell) => SurfaceCapability {
                window: dregg_firmament::Capability::surface(cell, rights.clone()),
                fetch_allow,
                navigate_allow,
                permissions,
            },
            None => SurfaceCapability {
                window: dregg_firmament::Capability {
                    target: self.held.window.target.clone(),
                    rights: rights.clone(),
                },
                fetch_allow,
                navigate_allow,
                permissions,
            },
        };

        // ANTI-AMPLIFICATION TOOTH (always on, fail-closed). The minted projection
        // MUST attenuate BOTH the held authority and the lineage on EVERY axis —
        // window rights (the REAL `is_attenuation`) AND the fetch/navigate/permission
        // sets (`⊆` both inputs). If for any reason the meet did not (a bug in
        // `meet_rights`/`intersect_allow`), we REFUSE rather than ship an amplified
        // cap to a viewer. A `debug_assert` would let a release build leak it; this
        // hard gate is the anti-ghost tooth the membrane is for. The honest path
        // (`meet_rights` returning the narrower, the sets intersecting) always
        // satisfies this — the gate only ever bites a genuine amplification.
        if !surface_attenuates_both(&self.held, &surface)
            || !surface_attenuates_both(lineage, &surface)
        {
            return Err(RehydrateError::Amplification);
        }
        Ok(surface)
    }

    /// **Compose** a reacquisition hop A→B→C: derive a NEW membrane for a downstream
    /// viewer (C) whose held authority is `requested` — REFUSING any request that
    /// would amplify beyond what THIS membrane's viewer (B) actually holds.
    ///
    /// `REHYDRATABLE-SURFACES.md` residual #1: "how attenuation composes across
    /// chained reacquisitions (A membranes to B, B reshares to C) — that is a
    /// protocol … the same `is_attenuation` lattice … lifted to projection
    /// composition." This is that lift: the reshare is admitted *iff* `requested` is
    /// an attenuation of `held` on EVERY axis — window rights (the REAL
    /// `is_attenuation`), fetch/navigate allowlists (`⊆`), permissions (`⊆`).
    ///
    /// The anti-ghost tooth: C can NEVER receive more authority than B held. A
    /// reshare that tries to widen any axis is [`RehydrateError::Amplification`].
    pub fn reshare(&self, requested: SurfaceCapability) -> Result<Membrane, RehydrateError> {
        // Window rights: requested must attenuate held (the REAL gate).
        if !is_attenuation(&self.held.window.rights, &requested.window.rights) {
            return Err(RehydrateError::Amplification);
        }
        // Fetch allowlist: requested reach must be ⊆ held reach.
        if !allow_is_subset(&self.held.fetch_allow, &requested.fetch_allow) {
            return Err(RehydrateError::Amplification);
        }
        // Navigate allowlist: same.
        if !allow_is_subset(&self.held.navigate_allow, &requested.navigate_allow) {
            return Err(RehydrateError::Amplification);
        }
        // Permissions: requested ⊆ held.
        if !requested.permissions.is_subset(&self.held.permissions) {
            return Err(RehydrateError::Amplification);
        }
        Ok(Membrane::new(requested))
    }
}

/// Rehydrate a [`Sturdyref`] through a [`Membrane`]: the membrane-negotiated
/// reacquisition returning the per-viewer [`Projection`] + its [`Rehydration`]
/// liveness-type.
///
/// `REHYDRATABLE-SURFACES.md` "the endgame": the screenshot is UX; the substance is
/// the attested, per-viewer, liveness-typed re-expansion of a certified projection
/// of a witnessed scene. This function is that re-expansion:
///
/// 1. **fetch = verified turn returning attested content** — resolve the
///    sturdyref's `dregg://` ref against the [`WebOfCells`] (the existing attested
///    cross-cell read), and VERIFY the attestation chain before anything else. A
///    tampered/forged/dead fetch returns [`RehydrateError::Fetch`] and NO projection
///    is minted (the bytes never reach a renderer);
/// 2. **per-viewer projection** — the membrane re-derives `(held) ∧ (lineage)`
///    through the REAL attenuation lattice ([`Membrane::project`]); two viewers with
///    different held caps get DIFFERENT projections of the SAME sturdyref;
/// 3. **liveness-type** — DERIVED from the source context's witness-log
///    ([`Sturdyref::liveness`]): `ReplayedDeterministic` iff every interaction was
///    an attested turn, `ReconstructedApproximate` iff any was ambient, `Live` iff
///    the sources are still reachable.
///
/// The fetch runs FIRST (and its result is verified) so an unattested scene never
/// yields a projection regardless of caps — confinement before relation.
pub fn rehydrate(
    sturdyref: &Sturdyref,
    membrane: &Membrane,
    web: &WebOfCells,
) -> Result<Projection, RehydrateError> {
    // (1) fetch = verified turn returning attested content. The `dregg://` resolve
    //     IS the rehydration's render-pass over the witness-graph (the compositor-PD
    //     seam). Verify the attestation chain BEFORE minting a projection — an
    //     unattested scene rehydrates to nothing.
    let (resource, chrome) = web.fetch(&sturdyref.uri)?;
    resource.verify()?; // FetchError -> RehydrateError on any chain failure.

    // (2) the per-viewer projection: (held authority) ∧ (the graph's permitted
    //     projections = the sturdyref's lineage), through the REAL lattice.
    let surface = membrane.project(&sturdyref.lineage)?;

    // (3) the liveness-type, DERIVED from the source context's witness-log.
    let liveness = sturdyref.liveness();

    Ok(Projection {
        surface,
        resource,
        chrome,
        liveness,
    })
}

// ──────────────────────────────────────────────────────────────────────────────
// lattice helpers — the meet/subset operations the membrane composes, all over the
// REAL `is_attenuation`. (No parallel rights model: `meet_rights` decides purely by
// asking `is_attenuation` which of two `AuthRequired`s is the narrower.)
// ──────────────────────────────────────────────────────────────────────────────

/// The **meet** of two `AuthRequired`s under the real attenuation lattice: the
/// narrower of the two, or `None` if they are incomparable.
///
/// `a` is narrower-or-equal to `b` iff `is_attenuation(b, a)` (`a ⊆ b`). So:
/// - if `a ⊆ b`, the meet is `a` (the narrower);
/// - else if `b ⊆ a`, the meet is `b`;
/// - else they are incomparable (e.g. two distinct `Custom { vk_hash }`, or
///   `Signature` vs `Proof`) — there is no single authority both admit as an
///   attenuation, so the projection is refused.
///
/// This is purely a function of `is_attenuation` — the membrane invents no ordering
/// of its own.
fn meet_rights(a: &AuthRequired, b: &AuthRequired) -> Option<AuthRequired> {
    if is_attenuation(b, a) {
        // a ⊆ b — a is the narrower (or equal).
        Some(a.clone())
    } else if is_attenuation(a, b) {
        // b ⊆ a — b is the narrower.
        Some(b.clone())
    } else {
        None
    }
}

/// Intersect two allowlists (where `None` is the wildcard "all origins"). The
/// result permits exactly the origins BOTH permit:
/// - `None ∩ x = x` (wildcard meets anything → that thing);
/// - `Some(p) ∩ Some(q) = Some(p ∩ q)`.
///
/// Total (no refusal): an intersection always exists and is `⊆` both inputs — the
/// projection meet narrows, it never widens.
fn intersect_allow(
    a: &Option<BTreeSet<String>>,
    b: &Option<BTreeSet<String>>,
) -> Option<BTreeSet<String>> {
    match (a, b) {
        (None, None) => None,
        (None, Some(s)) | (Some(s), None) => Some(s.clone()),
        (Some(p), Some(q)) => Some(p.intersection(q).cloned().collect()),
    }
}

/// Is `child` allowlist `⊆` `parent` allowlist (no amplification on a reshare)?
/// Semantics with `None` = wildcard:
/// - `child = None` (wildcard) is `⊆` `parent` only if `parent` is ALSO wildcard
///   (a concrete parent does not admit a wildcard child — that would widen);
/// - `parent = None` (wildcard) admits any `child`;
/// - both concrete: the usual `child ⊆ parent`.
fn allow_is_subset(parent: &Option<BTreeSet<String>>, child: &Option<BTreeSet<String>>) -> bool {
    match (parent, child) {
        (None, _) => true,        // wildcard parent admits anything.
        (Some(_), None) => false, // concrete parent does NOT admit a wildcard child.
        (Some(p), Some(c)) => c.is_subset(p),
    }
}

/// Does `child` attenuate `parent` on EVERY surface-authority axis? Window rights
/// via the REAL `is_attenuation` (`child ⊆ parent`), fetch/navigate allowlists +
/// permissions via `⊆`. The always-on anti-amplification tooth the membrane's
/// [`Membrane::project`] applies to its minted projection against BOTH inputs:
/// a projection that fails this on either input is a leak and is REFUSED.
fn surface_attenuates_both(parent: &SurfaceCapability, child: &SurfaceCapability) -> bool {
    is_attenuation(&parent.window.rights, &child.window.rights)
        && allow_is_subset(&parent.fetch_allow, &child.fetch_allow)
        && allow_is_subset(&parent.navigate_allow, &child.navigate_allow)
        && child.permissions.is_subset(&parent.permissions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::Capability;
    use dregg_types::CellId;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn origins(list: &[&str]) -> BTreeSet<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    /// Publish a page into a real web-of-cells and build a sturdyref over it,
    /// carrying `lineage` + a given witness-log + reachability. Returns
    /// `(web, sturdyref)`.
    fn published_sturdyref(
        seed: u8,
        lineage: SurfaceCapability,
        log: InteractionLog,
        sources_reachable: bool,
    ) -> (WebOfCells, Sturdyref) {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(seed, b"<h1>a rehydratable surface</h1>", "dregg://surface");
        let sturdyref = Sturdyref::new(uri, lineage, log, sources_reachable);
        (web, sturdyref)
    }

    /// A genuine, structurally-valid attestation usable as a witness for a
    /// witnessed interaction — built by actually publishing+fetching so the
    /// `AttestedRoot` is the REAL one the web-of-cells produces (v4-complete +
    /// quorum), not a hand-forged struct.
    fn a_real_witness() -> AttestedRoot {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(200, b"witnessed turn", "dregg://w");
        let (resource, _chrome) = web.fetch(&uri).expect("fetch resolves");
        assert!(resource.verify().is_ok());
        resource.attested_root
    }

    // ── Property 1: the liveness-type is a DERIVED confinement readout. ──

    #[test]
    fn liveness_is_derived_replayed_when_every_interaction_is_witnessed() {
        // A context whose every external interaction was a `dregg://` attested
        // fetch (witnessed) rehydrates ReplayedDeterministic — the confined
        // fragment, BY CONSTRUCTION (derived, not assigned).
        let witness = a_real_witness();
        let mut log = InteractionLog::new();
        log.record_attested_fetch(DreggUri::new(cid(40)), witness.clone());
        log.record_attested_fetch(DreggUri::new(cid(41)), witness);
        assert!(log.all_witnessed());
        assert_eq!(log.ambient_count(), 0);

        // sources gone → not Live; every interaction witnessed → ReplayedDeterministic.
        assert_eq!(
            Rehydration::classify(&log, false),
            Rehydration::ReplayedDeterministic
        );
    }

    #[test]
    fn liveness_is_derived_reconstructed_when_any_interaction_is_ambient() {
        // The OTHER polarity: a context that touched even ONE ambient (un-witnessed)
        // interaction is intrinsically ReconstructedApproximate — the thing that
        // made it non-deterministic was never witnessed.
        let witness = a_real_witness();
        let mut log = InteractionLog::new();
        log.record_attested_fetch(DreggUri::new(cid(42)), witness); // witnessed
        log.record_ambient("raw fetch https://ad.example.com"); // AMBIENT
        assert!(!log.all_witnessed());
        assert_eq!(log.ambient_count(), 1);

        assert_eq!(
            Rehydration::classify(&log, false),
            Rehydration::ReconstructedApproximate
        );
        assert!(!Rehydration::classify(&log, false).is_faithful());
    }

    #[test]
    fn liveness_is_live_when_sources_reachable_regardless_of_log() {
        // Live dominates: if the source contexts are still reachable, you reconnect
        // to the running scene whatever the log says.
        let mut log = InteractionLog::new();
        log.record_ambient("anything");
        assert_eq!(Rehydration::classify(&log, true), Rehydration::Live);
    }

    #[test]
    fn an_empty_log_replays_deterministically() {
        // A context that did nothing external is vacuously confined.
        let log = InteractionLog::new();
        assert!(log.all_witnessed());
        assert_eq!(
            Rehydration::classify(&log, false),
            Rehydration::ReplayedDeterministic
        );
    }

    #[test]
    fn a_structurally_invalid_attestation_is_not_witnessed() {
        // ANTI-TOY tooth on "witnessed": a purported attested fetch whose
        // AttestedRoot does NOT structurally hold (legacy v3, no receipt-stream
        // binding, or no quorum) is NOT witnessed — it cannot have captured the
        // non-determinism. So a log carrying only such a fetch reconstructs, it
        // does NOT replay-deterministic.
        let bogus = AttestedRoot::new_legacy([0u8; 32], 0, 0, vec![], None, 1); // v3, no quorum
        assert!(!bogus.is_v4_receipt_complete());
        let i = Interaction::attested_fetch(DreggUri::new(cid(43)), bogus);
        assert!(
            !i.is_witnessed(),
            "an attestation that doesn't hold is not a witness"
        );

        let mut log = InteractionLog::new();
        log.record(i);
        assert!(!log.all_witnessed());
        assert_eq!(
            Rehydration::classify(&log, false),
            Rehydration::ReconstructedApproximate
        );
    }

    #[test]
    fn liveness_ordering_is_more_true_to_less() {
        // The Ord derive encodes "more true/confined" > "less", so a chained
        // reacquisition can take the min to DOWNGRADE honestly.
        assert!(Rehydration::Live > Rehydration::ReplayedDeterministic);
        assert!(Rehydration::ReplayedDeterministic > Rehydration::ReconstructedApproximate);
        assert_eq!(
            Rehydration::ReplayedDeterministic.min(Rehydration::ReconstructedApproximate),
            Rehydration::ReconstructedApproximate
        );
    }

    // ── Property 2: two viewers rehydrate DIFFERENT projections of the SAME ref. ──

    #[test]
    fn two_viewers_with_different_caps_get_different_projections() {
        // The lineage permits {a, b}; viewer-1 holds {a}, viewer-2 holds {b}. Each
        // rehydrates the SAME sturdyref to a DIFFERENT projection (per-viewer
        // frustum), and each projection is ⊆ both its held caps and the lineage.
        let lineage = SurfaceCapability::scoped(
            cid(50),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com"]),
            [],
        );
        let (web, sturdyref) =
            published_sturdyref(50, lineage.clone(), InteractionLog::new(), false);

        let viewer1 = Membrane::new(SurfaceCapability::scoped(
            cid(51),
            AuthRequired::Either,
            origins(&["https://a.example.com"]),
            [],
        ));
        let viewer2 = Membrane::new(SurfaceCapability::scoped(
            cid(52),
            AuthRequired::Either,
            origins(&["https://b.example.com"]),
            [],
        ));

        let p1 = rehydrate(&sturdyref, &viewer1, &web).expect("viewer1 rehydrates");
        let p2 = rehydrate(&sturdyref, &viewer2, &web).expect("viewer2 rehydrates");

        // DIFFERENT projections of the SAME sturdyref.
        assert_ne!(p1.surface, p2.surface);
        // Viewer 1 may reach a, not b; viewer 2 may reach b, not a.
        assert!(p1.surface.may_fetch("https://a.example.com"));
        assert!(!p1.surface.may_fetch("https://b.example.com"));
        assert!(p2.surface.may_fetch("https://b.example.com"));
        assert!(!p2.surface.may_fetch("https://a.example.com"));
        // Both are bound to the SAME origin cell (the thing being re-viewed).
        assert_eq!(p1.surface.cell(), Some(cid(50)));
        assert_eq!(p2.surface.cell(), Some(cid(50)));
    }

    #[test]
    fn the_projection_is_the_meet_never_wider_than_held_or_lineage() {
        // A viewer that HOLDS more than the lineage permits is still capped by the
        // lineage (and vice-versa) — the projection is the meet of both.
        let lineage = SurfaceCapability::scoped(
            cid(60),
            AuthRequired::Signature, // read-only lineage
            origins(&["https://a.example.com"]),
            [],
        );
        let (web, sturdyref) =
            published_sturdyref(60, lineage.clone(), InteractionLog::new(), false);

        // The viewer holds the WILDCARD (None fetch) + broader window rights (Either).
        let viewer = Membrane::new(SurfaceCapability::root(cid(61), AuthRequired::Either));
        let p = rehydrate(&sturdyref, &viewer, &web).expect("rehydrates");

        // Window rights are the MEET: Signature (the narrower lineage), not Either.
        assert_eq!(p.surface.window.rights, AuthRequired::Signature);
        // The wildcard viewer is held to the lineage's concrete reach.
        assert!(p.surface.may_fetch("https://a.example.com"));
        assert!(!p.surface.may_fetch("https://other.example.com"));
        // The meet attenuates BOTH inputs (the proven-lattice property).
        assert!(is_attenuation(
            &viewer.held().window.rights,
            &p.surface.window.rights
        ));
        assert!(is_attenuation(
            &lineage.window.rights,
            &p.surface.window.rights
        ));
    }

    #[test]
    fn incomparable_window_rights_refuse_the_projection() {
        // If the held authority and the lineage are INCOMPARABLE (Signature vs
        // Proof — neither attenuates the other), there is no projection both admit:
        // the membrane refuses (Amplification), no surface is minted.
        let lineage = SurfaceCapability::root(cid(70), AuthRequired::Signature);
        let (web, sturdyref) = published_sturdyref(70, lineage, InteractionLog::new(), false);
        let viewer = Membrane::new(SurfaceCapability::root(cid(71), AuthRequired::Proof));

        assert_eq!(
            rehydrate(&sturdyref, &viewer, &web),
            Err(RehydrateError::Amplification)
        );
    }

    // ── Property 3 + anti-ghost: a reshare A→B→C that amplifies is REFUSED. ──

    #[test]
    fn a_reshare_chain_attenuates_and_an_amplifying_reshare_is_refused() {
        // A→B→C composition through the REAL is_attenuation per hop.
        // A holds {a, b} (Either). B reshares to {a} (Either) — a strict
        // attenuation, ADMITTED. C tries to reshare from B back UP to {a, b} — an
        // AMPLIFICATION beyond what B held — REFUSED.
        let a = Membrane::new(SurfaceCapability::scoped(
            cid(80),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com"]),
            [],
        ));

        // A→B: narrow to {a}. Admitted.
        let b = a
            .reshare(SurfaceCapability::scoped(
                cid(81),
                AuthRequired::Either,
                origins(&["https://a.example.com"]),
                [],
            ))
            .expect("a narrowing reshare A->B is admitted");
        assert!(b.held().may_fetch("https://a.example.com"));
        assert!(!b.held().may_fetch("https://b.example.com"));

        // B→C: try to amplify back to {a, b} (b ⊄ {a}) — REFUSED (the anti-ghost
        // tooth: C cannot receive more than B held).
        let amplify = b.reshare(SurfaceCapability::scoped(
            cid(82),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com"]),
            [],
        ));
        assert_eq!(amplify, Err(RehydrateError::Amplification));

        // B→C narrowing further (to {} / nothing) IS admitted.
        let c = b
            .reshare(SurfaceCapability::scoped(
                cid(83),
                AuthRequired::Either,
                origins(&[]),
                [],
            ))
            .expect("a further-narrowing reshare B->C is admitted");
        assert!(!c.held().may_fetch("https://a.example.com"));
    }

    #[test]
    fn a_reshare_that_widens_window_rights_is_refused() {
        // The window-rights axis of the reshare tooth: B holds Signature
        // (read-only); a reshare to None (full) is a WIDENING — refused by the REAL
        // is_attenuation.
        let b = Membrane::new(SurfaceCapability::root(cid(90), AuthRequired::Signature));
        let widen = b.reshare(SurfaceCapability::root(cid(91), AuthRequired::None));
        assert_eq!(widen, Err(RehydrateError::Amplification));

        // An equal/narrowing reshare is fine.
        let ok = b.reshare(SurfaceCapability::root(cid(92), AuthRequired::Signature));
        assert!(ok.is_ok());
    }

    #[test]
    fn a_reshare_that_gains_a_permission_is_refused() {
        // The permissions axis: B holds Geolocation only; a reshare asking for
        // Camera (which B lacks) is refused.
        let b = Membrane::new(SurfaceCapability::scoped(
            cid(95),
            AuthRequired::Either,
            origins(&["https://x.example.com"]),
            [PermissionKind::Geolocation],
        ));
        let mut want = BTreeSet::new();
        want.insert(PermissionKind::Camera);
        let widen = b.reshare(SurfaceCapability {
            window: Capability::surface(cid(96), AuthRequired::Either),
            fetch_allow: Some(origins(&["https://x.example.com"])),
            navigate_allow: Some(origins(&["https://x.example.com"])),
            permissions: want,
        });
        assert_eq!(widen, Err(RehydrateError::Amplification));
    }

    #[test]
    fn a_reshared_membrane_then_rehydrates_its_attenuated_projection() {
        // End-to-end of the chain: A reshares to B; B (a downstream viewer)
        // rehydrates the SAME sturdyref and gets a projection ⊆ B's reshared
        // authority ⊆ A. The reshare composes with the lineage meet.
        let lineage = SurfaceCapability::scoped(
            cid(100),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com"]),
            [],
        );
        let (web, sturdyref) = published_sturdyref(100, lineage, InteractionLog::new(), false);

        let a = Membrane::new(SurfaceCapability::scoped(
            cid(101),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com"]),
            [],
        ));
        // A→B: narrow to {a}.
        let b = a
            .reshare(SurfaceCapability::scoped(
                cid(102),
                AuthRequired::Either,
                origins(&["https://a.example.com"]),
                [],
            ))
            .expect("A->B admitted");

        // B rehydrates: projection = (B held {a}) ∧ (lineage {a,b}) = {a}.
        let p = rehydrate(&sturdyref, &b, &web).expect("B rehydrates");
        assert!(p.surface.may_fetch("https://a.example.com"));
        assert!(!p.surface.may_fetch("https://b.example.com")); // narrowed at the reshare.
    }

    #[test]
    fn the_membrane_round_trip_holds_the_anti_amplification_tooth_on_every_hop() {
        // THE MEMBRANE ROUND-TRIP at the surface-cap layer (the companion to
        // shared_fork's World-layer round-trip): mint a sturdyref behind a membrane
        // → A rehydrates a per-viewer projection → A reshares to C → C rehydrates.
        // The always-on anti-amplification tooth holds on EVERY hop: each minted
        // projection attenuates BOTH its held authority AND the lineage, on EVERY
        // axis (window rights, fetch/navigate allowlists, permissions). The honest
        // path never trips the hardened gate.
        let lineage = SurfaceCapability::scoped(
            cid(150),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com", "https://c.example.com"]),
            [PermissionKind::Geolocation, PermissionKind::Clipboard],
        );
        let (web, sturdyref) =
            published_sturdyref(150, lineage.clone(), InteractionLog::new(), false);

        // Hop 1 — A (holds a narrower fetch set + one permission) rehydrates.
        let a = Membrane::new(SurfaceCapability::scoped(
            cid(151),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com"]),
            [PermissionKind::Geolocation],
        ));
        let pa = rehydrate(&sturdyref, &a, &web).expect("A rehydrates");
        // The projection attenuates BOTH A's held authority AND the lineage.
        assert!(surface_attenuates_both(a.held(), &pa.surface), "A's projection ⊆ A held");
        assert!(surface_attenuates_both(&lineage, &pa.surface), "A's projection ⊆ lineage");
        // Concretely: the fetch set is the intersection, the permission set the meet.
        assert!(pa.surface.may_fetch("https://a.example.com"));
        assert!(!pa.surface.may_fetch("https://c.example.com")); // A never held it.
        assert!(pa.surface.has_permission(PermissionKind::Geolocation));
        assert!(!pa.surface.has_permission(PermissionKind::Clipboard)); // A never held it.

        // Hop 2 — A reshares to C (a strict attenuation: drop a fetch origin + the
        // permission), then C rehydrates the SAME sturdyref.
        let c = a
            .reshare(SurfaceCapability::scoped(
                cid(152),
                AuthRequired::Either,
                origins(&["https://a.example.com"]),
                [],
            ))
            .expect("A->C reshare admitted (strict attenuation)");
        let pc = rehydrate(&sturdyref, &c, &web).expect("C rehydrates");
        assert!(surface_attenuates_both(c.held(), &pc.surface), "C's projection ⊆ C held");
        assert!(surface_attenuates_both(&lineage, &pc.surface), "C's projection ⊆ lineage");
        // C is strictly narrower than A on every axis (the chain attenuates).
        assert!(pc.surface.may_fetch("https://a.example.com"));
        assert!(!pc.surface.may_fetch("https://b.example.com")); // dropped at the reshare.
        assert!(!pc.surface.has_permission(PermissionKind::Geolocation)); // dropped at the reshare.
    }

    // ── The fetch is a verified turn: an unattested scene yields NO projection. ──

    #[test]
    fn a_dead_ref_yields_no_projection() {
        // The fetch runs first and is verified: a dead `dregg://` ref rehydrates to
        // a Fetch error, NO projection (regardless of caps).
        let web = WebOfCells::new(3);
        let dead = Sturdyref::new(
            DreggUri::new(cid(120)),
            SurfaceCapability::root(cid(120), AuthRequired::Either),
            InteractionLog::new(),
            false,
        );
        let viewer = Membrane::new(SurfaceCapability::root(cid(121), AuthRequired::Either));
        assert_eq!(
            rehydrate(&dead, &viewer, &web),
            Err(RehydrateError::Fetch(FetchError::OriginNotFound))
        );
    }

    #[test]
    fn a_tampered_scene_yields_no_projection_even_with_full_caps() {
        // Confinement before relation: even a viewer holding full authority gets NO
        // projection from a scene whose attestation does not verify. We simulate a
        // lying node by drifting the byte store post-publish (caught at fetch).
        let lineage = SurfaceCapability::root(cid(130), AuthRequired::Either);
        let mut web = WebOfCells::new(3);
        let uri = web.publish(130, b"the committed scene", "dregg://scene");

        // Drift the node's bytes away from the commitment (a lying node).
        for entry in web.bytes_store.iter_mut() {
            if entry.0 == uri.cell {
                entry.1 = b"injected bytes the origin never committed".to_vec();
            }
        }
        let sturdyref = Sturdyref::new(uri, lineage, InteractionLog::new(), false);
        let viewer = Membrane::new(SurfaceCapability::root(cid(131), AuthRequired::None)); // full
        assert_eq!(
            rehydrate(&sturdyref, &viewer, &web),
            Err(RehydrateError::Fetch(
                FetchError::ContentDoesNotMatchCommitment
            ))
        );
    }

    #[test]
    fn rehydrate_carries_the_derived_liveness_and_ledger_chrome() {
        // The full happy path: a confined source (all attested) rehydrates with the
        // DERIVED ReplayedDeterministic liveness + the ledger-drawn chrome.
        let witness = a_real_witness();
        let mut log = InteractionLog::new();
        log.record_attested_fetch(DreggUri::new(cid(140)), witness);

        let lineage = SurfaceCapability::root(cid(141), AuthRequired::Either);
        let (web, sturdyref) = published_sturdyref(141, lineage, log, false);
        let viewer = Membrane::new(SurfaceCapability::root(cid(142), AuthRequired::Either));

        let p = rehydrate(&sturdyref, &viewer, &web).expect("rehydrates");
        // The liveness-type is the DERIVED one (every interaction witnessed → replay).
        assert_eq!(p.liveness, Rehydration::ReplayedDeterministic);
        assert!(p.liveness.is_faithful());
        // The chrome is ledger-drawn (cell id + committed URL), not the page.
        assert_eq!(p.chrome.committed_url.as_deref(), Some("dregg://surface"));
        // The attestation the projection carries verifies.
        assert!(p.resource.verify().is_ok());
    }

    // ── Anti-toy: the projection IS a real firmament cap; the meet uses the
    //    REAL is_attenuation. ──

    #[test]
    fn the_projection_is_a_real_firmament_surface_cap() {
        let lineage = SurfaceCapability::root(cid(150), AuthRequired::Either);
        let (web, sturdyref) = published_sturdyref(150, lineage, InteractionLog::new(), false);
        let viewer = Membrane::new(SurfaceCapability::root(cid(151), AuthRequired::Either));
        let p = rehydrate(&sturdyref, &viewer, &web).expect("rehydrates");
        // The projection's surface IS a firmament Capability with a Surface target.
        assert!(p.surface.window.target.is_surface());
        assert_eq!(p.surface.cell(), Some(cid(150)));
    }

    #[test]
    fn meet_rights_is_purely_is_attenuation() {
        // The meet invents no ordering: it is exactly "the narrower under
        // is_attenuation", or None when incomparable.
        assert_eq!(
            meet_rights(&AuthRequired::Either, &AuthRequired::Signature),
            Some(AuthRequired::Signature) // Signature ⊆ Either
        );
        assert_eq!(
            meet_rights(&AuthRequired::None, &AuthRequired::Either),
            Some(AuthRequired::Either) // Either ⊆ None
        );
        assert_eq!(
            meet_rights(&AuthRequired::Signature, &AuthRequired::Proof),
            None // incomparable
        );
        // And it agrees with is_attenuation on the result.
        let m = meet_rights(&AuthRequired::Either, &AuthRequired::Signature).unwrap();
        assert!(is_attenuation(&AuthRequired::Either, &m));
        assert!(is_attenuation(&AuthRequired::Signature, &m));
    }
}
