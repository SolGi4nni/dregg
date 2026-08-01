//! THE FRUSTUM / SNAPSHOT EDITOR — the share-with-attenuation surface.
//!
//! `docs/desktop-os-research/REHYDRATABLE-SURFACES.md`: a deos "screenshot" is a
//! **paused camera on a witnessed scene** behind a **membrane** — sharing it is
//! not "I leaked my session" but "I extended a revocable, attenuated, per-viewer
//! right to re-view". This module is the **pre-send editor** where you SCULPT that
//! share before it leaves your hands:
//!
//!   1. **Cull the frustum** — toggle which presentation lenses + which sub-objects
//!      (a cell's affordances) are IN the shared slice. Culling can only NARROW the
//!      boundary (a `cull_*` strictly shrinks the slice; the cull set starts FULL).
//!   2. **Pare the authority** — an [`AttenuationDial`] over the held window cap.
//!      The recipient gets only the rights the dial designates, validated by the
//!      REAL [`is_attenuation`] (`granted ⊆ held`): the dial REFUSES an amplifying
//!      choice IN-BAND ([`SnapshotEditor::pare_to`] surfaces the refusal), never
//!      silently widens.
//!   3. **Live verification** — as you edit, [`SnapshotEditor::verify`] reports
//!      whether the pare is a sound attenuation AND what a given recipient would
//!      ACTUALLY see (the membrane-projected preview = the REAL
//!      [`AffordanceSnapshot::rehydrate_for`] through the same `is_attenuation`).
//!   4. **Share** — [`SnapshotEditor::share`] produces the [`SharedArtifact`]: the
//!      culled [`UiSnapshot`] + the attenuated cap + the culled
//!      [`AffordanceSnapshot`] (the membrane scope) + a revocation handle. A
//!      `share()` that would amplify is REFUSED (returns the refusal); it is not
//!      possible to mint an over-wide artifact through this editor.
//!
//! ## The org-settings register (the familiar UX, the sound substrate)
//!
//! `REHYDRATABLE-SURFACES.md` "the membrane negotiation IS a GitHub-org settings
//! page": teams = capability groups · roles (read/triage/write/admin) = the
//! attenuation lattice · visibility = the projection/frustum scope · member mgmt =
//! grant/revoke. This editor IS that page for ONE shared slice: the frustum cull is
//! *visibility*, the attenuation dial is the *role*, the recipient preview is
//! *"what this member would see"*, and [`SharedArtifact::revoke`] is *removing the
//! member*. Familiar surface; under it, every primitive is the REAL one.
//!
//! ## Hard reuse (no reinvented attenuation, no reinvented snapshot)
//!
//!   * the SNAPSHOT is [`crate::ui_snapshot::UiSnapshot`] (the witness-cursor camera
//!     the live inspector already paused) — we carry it, we do not re-derive it;
//!   * the AFFORDANCE FRUSTUM is [`crate::affordance::AffordanceSnapshot`] +
//!     `rehydrate_for` (the per-viewer membrane projection through `is_attenuation`);
//!   * the ATTENUATION DIAL is [`crate::cap_inspector::AttenuationDial`] (which
//!     itself rides the REAL [`dregg_firmament::Capability::attenuate`] +
//!     [`is_attenuation`]) — the dial REFUSES a widening fail-closed;
//!   * the NO-AMPLIFICATION GATE is the GENUINE [`dregg_cell::is_attenuation`],
//!     the same lattice the cap crown + the membrane prove.
//!
//! gpui-free + `cargo test`-able exactly as `ui_snapshot.rs`/`cap_inspector.rs` are.

use dregg_cell::{is_attenuation, AuthRequired};
use dregg_firmament::{Capability, Rights, Target};

use crate::affordance::{AffordanceSnapshot, AffordanceSurface};
use crate::cap_inspector::AttenuationDial;
use crate::presentable::{Gadget, GadgetInput, GadgetValidation, PresentationKind};
use crate::surface::{SurfaceCapability, SurfaceId};
use crate::ui_snapshot::UiSnapshot;
use dregg_cell::{Credential, Requirement};
use dregg_types::CellId;

// ===========================================================================
// §1 — the frustum: which lenses + which sub-objects are IN the shared slice.
// ===========================================================================

/// The seven presentation lenses a [`UiSnapshot`] could carry, the toggleable
/// faces of the frustum. The cull set starts FULL (everything the camera saw is
/// in the slice); each [`SnapshotEditor::cull_lens`] can only REMOVE a face — the
/// boundary only narrows, never grows past what was captured.
pub const ALL_LENSES: [PresentationKind; 7] = [
    PresentationKind::RawFields,
    PresentationKind::Graph,
    PresentationKind::DomainVisual,
    PresentationKind::Affordances,
    PresentationKind::Provenance,
    PresentationKind::Invariant,
    PresentationKind::Source,
];

/// The **frustum boundary** the editor sculpts — which lenses + which sub-objects
/// (a focused cell's affordances) are IN the shared slice.
///
/// It is the *culling boundary* of `REHYDRATABLE-SURFACES.md`: tiny by
/// construction (names + flags, never projected bytes). Two narrowing axes:
///
///   * `lenses` — the [`PresentationKind`]s still in the slice (starts FULL);
///   * `affordance_names` — the sub-objects (a cell's named affordances) still in
///     the slice (starts = every affordance the live surface published).
///
/// Both are *cull-only*: a toggle can remove a member, the editor never inserts a
/// member the live capture did not contain (you cannot share more than you saw).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frustum {
    /// The lenses still inside the slice (a subset of [`ALL_LENSES`]).
    lenses: Vec<PresentationKind>,
    /// The affordance names still inside the slice (a subset of the captured set).
    affordance_names: Vec<String>,
    /// The full captured affordance set — the ceiling the cull cannot exceed (so a
    /// re-toggle of a culled name restores it but cannot ADD a foreign name).
    captured_affordances: Vec<String>,
}

impl Frustum {
    /// A FULL frustum: every lens + every captured affordance is in the slice (the
    /// editor starts here and only narrows).
    pub fn full(captured_affordances: Vec<String>) -> Self {
        Frustum {
            lenses: ALL_LENSES.to_vec(),
            affordance_names: captured_affordances.clone(),
            captured_affordances,
        }
    }

    /// The lenses currently in the slice (sorted by the canonical order).
    pub fn lenses(&self) -> &[PresentationKind] {
        &self.lenses
    }

    /// The affordance names currently in the slice (the culled sub-object set).
    pub fn affordance_names(&self) -> &[String] {
        &self.affordance_names
    }

    /// Is `lens` currently in the slice?
    pub fn has_lens(&self, lens: PresentationKind) -> bool {
        self.lenses.contains(&lens)
    }

    /// Is the affordance named `name` currently in the slice?
    pub fn has_affordance(&self, name: &str) -> bool {
        self.affordance_names.iter().any(|n| n == name)
    }

    /// Toggle a lens IN/OUT of the slice. Cull-only in spirit: removing narrows;
    /// re-adding restores a lens that was always a member of [`ALL_LENSES`] (the
    /// captured ceiling). Returns the new membership of `lens`.
    pub fn toggle_lens(&mut self, lens: PresentationKind) -> bool {
        if let Some(pos) = self.lenses.iter().position(|l| *l == lens) {
            self.lenses.remove(pos);
            false
        } else if ALL_LENSES.contains(&lens) {
            // Restore in canonical order (the ceiling membership).
            self.lenses.push(lens);
            self.lenses
                .sort_by_key(|l| ALL_LENSES.iter().position(|x| x == l).unwrap_or(usize::MAX));
            true
        } else {
            false
        }
    }

    /// Toggle an affordance sub-object IN/OUT of the slice. The cull can ONLY
    /// re-add a name that was in the captured ceiling — it can never widen the
    /// slice to a sub-object the live capture did not contain. Returns the new
    /// membership of `name` (`false` if `name` is not a captured affordance).
    pub fn toggle_affordance(&mut self, name: &str) -> bool {
        if let Some(pos) = self.affordance_names.iter().position(|n| n == name) {
            self.affordance_names.remove(pos);
            false
        } else if self.captured_affordances.iter().any(|n| n == name) {
            self.affordance_names.push(name.to_string());
            self.affordance_names.sort();
            true
        } else {
            // Not a captured sub-object — refused (you cannot share what you did
            // not see). The slice is unchanged.
            false
        }
    }

    /// The captured ceiling of affordance names (the cull cannot exceed this).
    pub fn captured_affordances(&self) -> &[String] {
        &self.captured_affordances
    }
}

// ===========================================================================
// §2 — the editor: cull + pare + verify + share, over the REAL primitives.
// ===========================================================================

/// THE FRUSTUM / SNAPSHOT EDITOR — the pre-send sculpting surface.
///
/// It holds the captured [`UiSnapshot`] (the slice the camera paused on), the
/// backing cell whose affordances are the shareable sub-objects, the live
/// [`AffordanceSurface`] (the witness-graph the membrane projects through), the
/// [`Frustum`] being sculpted, and the [`AttenuationDial`] paring the authority.
///
/// Nothing here re-derives the snapshot or the attenuation: the snapshot is the
/// inspector's own paused camera, and every narrowing is the REAL `is_attenuation`.
#[derive(Clone, Debug)]
pub struct SnapshotEditor {
    /// The captured UI-slice snapshot — the camera the live inspector paused (the
    /// thing being shared). We carry it; we never re-derive it.
    snapshot: UiSnapshot,
    /// The backing cell whose affordances are the shareable sub-objects (the
    /// snapshot's focus cell — the membrane's origin).
    backing: CellId,
    /// The held window cap (the ceiling). Any pare must be `is_attenuation` of it.
    held: SurfaceCapability,
    /// The live affordance surface — the witness-graph the membrane projects
    /// through (`AffordanceSnapshot::rehydrate_for`). The source of truth: a cull
    /// can only share affordances that STILL exist here.
    surface: AffordanceSurface,
    /// The frustum being sculpted (cull-only).
    frustum: Frustum,
    /// The attenuation dial paring the authority (the REAL `AttenuationDial`).
    dial: AttenuationDial,
}

impl SnapshotEditor {
    /// Open the editor over a captured snapshot of the focused view.
    ///
    /// `snapshot` is the [`UiSnapshot`] the inspector paused; `surface` is the live
    /// [`AffordanceSurface`] of the focused cell (the sub-objects shareable + the
    /// witness-graph the membrane projects through); `held` is the window cap the
    /// operator holds (the attenuation ceiling). The frustum starts FULL (every
    /// lens + every captured affordance) and the dial starts over `held` (unset, so
    /// the form is incomplete until a tier is picked — fail-closed).
    pub fn open(snapshot: UiSnapshot, surface: AffordanceSurface, held: SurfaceCapability) -> Self {
        let captured: Vec<String> = surface.all_names();
        let backing = surface.cell;
        let dial = AttenuationDial::new(held.authority().clone());
        SnapshotEditor {
            snapshot,
            backing,
            held,
            surface,
            frustum: Frustum::full(captured),
            dial,
        }
    }

    /// The snapshot being shared (read-only).
    pub fn snapshot(&self) -> &UiSnapshot {
        &self.snapshot
    }

    /// The frustum being sculpted (read-only).
    pub fn frustum(&self) -> &Frustum {
        &self.frustum
    }

    /// The held window cap (the attenuation ceiling).
    pub fn held(&self) -> &SurfaceCapability {
        &self.held
    }

    // ── CULL THE FRUSTUM ────────────────────────────────────────────────────

    /// Toggle a presentation lens IN/OUT of the shared slice. Returns its new
    /// membership. Narrowing only narrows; re-adding restores a captured lens.
    pub fn cull_lens(&mut self, lens: PresentationKind) -> bool {
        self.frustum.toggle_lens(lens)
    }

    /// Toggle an affordance sub-object IN/OUT of the shared slice. Returns its new
    /// membership (`false` if `name` is not a captured affordance — the cull
    /// cannot widen past what was seen).
    pub fn cull_affordance(&mut self, name: &str) -> bool {
        self.frustum.toggle_affordance(name)
    }

    // ── PARE THE AUTHORITY ──────────────────────────────────────────────────

    /// The variant slugs the pare dial offers (the rights tiers — the lattice
    /// "roles" of the org-settings register).
    pub fn pare_choices(&self) -> Vec<String> {
        self.dial
            .fields()
            .into_iter()
            .find_map(|f| match f {
                crate::presentable::GadgetField::Enum { key, variants } if key == "rights" => {
                    Some(variants)
                }
                _ => None,
            })
            .unwrap_or_default()
    }

    /// **Pare the authority** to the rights tier named `tier_slug`. Drives the REAL
    /// [`AttenuationDial`] — which validates the narrowing with the GENUINE
    /// [`is_attenuation`]. Returns the dial's verdict: an amplifying choice yields
    /// [`PareOutcome::Refused`] (the dial REFUSES it in-band, fail-closed); a sound
    /// attenuation yields [`PareOutcome::Pared`] carrying the narrowed tier.
    pub fn pare_to(&mut self, tier_slug: &str) -> PareOutcome {
        // Use the Gadget trait surface — the real dial, no parallel narrowing.
        self.dial
            .set("rights", GadgetInput::Variant(tier_slug.to_string()));
        match self.dial.validate() {
            GadgetValidation::Ok => {
                // Build the attenuated cap through the REAL Capability::attenuate
                // (the dial rides it; a widening would have failed validation).
                match self.dial.build() {
                    Ok(cap) => PareOutcome::Pared {
                        rights: cap.rights.clone(),
                    },
                    Err(e) => PareOutcome::Refused {
                        reason: format!("the pare could not build: {e:?}"),
                    },
                }
            }
            GadgetValidation::Invalid { reason } => PareOutcome::Refused { reason },
        }
    }

    /// The attenuated firmament cap the current pare designates, if the pare is a
    /// sound attenuation (else `None` — the dial refuses to build a widening).
    pub fn pared_cap(&self) -> Option<Capability> {
        self.dial.build().ok()
    }

    // ── LIVE VERIFICATION ───────────────────────────────────────────────────

    /// **Verify** the current edit, live. Reports:
    ///   * `sound` — is the pare a legal attenuation of the held cap (the REAL
    ///     [`is_attenuation`]); `false` while the dial is unset or amplifying;
    ///   * `recipient_lenses` — the lenses the recipient would see (the culled
    ///     frustum);
    ///   * `recipient_affordances` — what a recipient holding the PARED cap would
    ///     ACTUALLY rehydrate: the membrane-projected preview = the REAL
    ///     [`AffordanceSnapshot::rehydrate_for`] over the live surface through the
    ///     same `is_attenuation`, CONFINED to the culled frustum. This is the
    ///     "what this member would see" of the org-settings page, computed by the
    ///     genuine membrane, not narrated.
    pub fn verify(&self) -> Verification {
        let pared = self.pared_cap();
        let sound = pared
            .as_ref()
            .map(|c| is_attenuation(&self.held.rights().clone(), &c.rights))
            .unwrap_or(false);

        // The membrane-projected preview: rehydrate the culled affordance snapshot
        // for a recipient holding the PARED cap (or, if not yet pared, NO cap → the
        // empty preview, the honest "an unset/over-wide pare grants nothing").
        let recipient_affordances = match &pared {
            Some(cap) => {
                let recipient_held = self.recipient_cap(cap.rights.clone());
                self.preview_for(&recipient_held)
            }
            None => Vec::new(),
        };

        Verification {
            sound,
            pared_rights: pared.map(|c| c.rights),
            recipient_lenses: self.frustum.lenses().to_vec(),
            recipient_affordances,
        }
    }

    /// The membrane-projected preview for a recipient holding `recipient_held`:
    /// the REAL [`AffordanceSnapshot::rehydrate_for`] over the live surface
    /// (through `is_attenuation`), then CONFINED to the culled frustum (a
    /// sub-object the operator culled out is removed even if the cap would admit
    /// it). This is exactly the per-viewer attenuated slice the recipient gets.
    pub fn preview_for(&self, recipient_held: &SurfaceCapability) -> Vec<String> {
        // The culled affordance snapshot (the membrane scope being shared).
        let snap = self.affordance_snapshot();
        // The REAL per-viewer membrane projection over the live surface.
        let rehydrated = snap.rehydrate_for(&self.surface, recipient_held);
        let mut names = rehydrated.names();
        // Confine to the cull (the operator may have removed sub-objects the cap
        // would otherwise admit — the frustum is the tighter boundary).
        names.retain(|n| self.frustum.has_affordance(n));
        names
    }

    // ── SHARE ───────────────────────────────────────────────────────────────

    /// **Share** — produce the revocable, attenuated, rehydratable artifact.
    ///
    /// The artifact is the culled [`UiSnapshot`] + the attenuated cap + the culled
    /// [`AffordanceSnapshot`] (the membrane scope) + a live revocation flag. A
    /// `share` whose pare is NOT a sound attenuation is REFUSED — it is not possible
    /// to mint an over-wide artifact through this editor (the no-amplification gate
    /// is in-band, surfaced). "Shared a screenshot" becomes "extended a revocable,
    /// attenuated, audited right to re-view a witnessed slice."
    pub fn share(&self) -> Result<SharedArtifact, ShareError> {
        let pared = self.pared_cap().ok_or(ShareError::PareIncomplete)?;
        // The no-amplification gate, IN-BAND: the pared rights MUST attenuate held.
        if !is_attenuation(&self.held.rights().clone(), &pared.rights) {
            return Err(ShareError::WouldAmplify {
                held: self.held.rights().clone(),
                pared: pared.rights.clone(),
            });
        }
        Ok(SharedArtifact {
            snapshot: self.snapshot,
            lenses: self.frustum.lenses().to_vec(),
            affordance_scope: self.affordance_snapshot(),
            attenuated_rights: pared.rights.clone(),
            attenuated_cap: pared,
            backing: self.backing,
            revoked: false,
        })
    }

    // ── helpers ─────────────────────────────────────────────────────────────

    /// The culled [`AffordanceSnapshot`] — the membrane scope being shared. It
    /// carries the backing cell + ONLY the affordance names still in the frustum
    /// (the sub-object cull). Tiny by construction (names, not data).
    fn affordance_snapshot(&self) -> AffordanceSnapshot {
        AffordanceSnapshot {
            cell: self.backing,
            affordance_names: self.frustum.affordance_names().to_vec(),
        }
    }

    /// Wrap a designated `rights` tier into a recipient-held [`SurfaceCapability`]
    /// over the backing cell — the cap a recipient would present to rehydrate. The
    /// surface id is the held cap's (the membrane binds to the same surface origin).
    fn recipient_cap(&self, rights: Rights) -> SurfaceCapability {
        SurfaceCapability::new(
            self.held.surface(),
            Capability {
                target: Target::Surface { cell: self.backing },
                rights,
            },
        )
    }
}

// ===========================================================================
// §3 — the outcomes: pare verdict · verification readout · the shared artifact.
// ===========================================================================

/// The verdict of [`SnapshotEditor::pare_to`] — the dial's in-band decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PareOutcome {
    /// The pare is a sound attenuation — the recipient gets `rights` (`⊆ held`).
    Pared { rights: AuthRequired },
    /// The pare would AMPLIFY (or the dial is incomplete) — REFUSED in-band,
    /// fail-closed, with the dial's own reason. The slice is unchanged.
    Refused { reason: String },
}

impl PareOutcome {
    /// `true` iff the pare was a sound attenuation.
    pub fn is_pared(&self) -> bool {
        matches!(self, PareOutcome::Pared { .. })
    }
}

/// The live verification readout — what the editor shows AS you edit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verification {
    /// Is the current pare a legal attenuation of the held cap (the REAL
    /// `is_attenuation`)? `false` while unset or amplifying — the share refuses.
    pub sound: bool,
    /// The rights the recipient would get (the pared tier), if pared.
    pub pared_rights: Option<AuthRequired>,
    /// The lenses the recipient would see (the culled frustum faces).
    pub recipient_lenses: Vec<PresentationKind>,
    /// What a recipient holding the PARED cap would ACTUALLY rehydrate — the
    /// membrane-projected, frustum-confined affordance set (the genuine
    /// per-viewer slice, not a narration).
    pub recipient_affordances: Vec<String>,
}

/// Why a [`SnapshotEditor::share`] was refused (the no-amplification gate, in-band).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShareError {
    /// The pare dial has not designated a (buildable) rights tier yet.
    PareIncomplete,
    /// The designated rights would AMPLIFY the held cap — refused fail-closed (you
    /// cannot mint an over-wide artifact). The same `is_attenuation` lattice.
    WouldAmplify {
        held: AuthRequired,
        pared: AuthRequired,
    },
}

/// THE SHARED ARTIFACT — the revocable, attenuated, rehydratable slice.
///
/// `REHYDRATABLE-SURFACES.md` "the unit was never the pixels or the data — it was
/// *the revocable right to renegotiate the connection*." This artifact IS that: a
/// [`UiSnapshot`] (the paused camera the recipient re-runs), the attenuated cap
/// (the role the recipient gets), the [`AffordanceSnapshot`] (the membrane scope —
/// the visibility), and a revocation flag (member removal). Sharing it is
/// extending a per-viewer, attenuated, audited right to re-view — never a session
/// leak.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedArtifact {
    /// The culled UI-slice snapshot (the paused camera — the recipient re-runs it).
    pub snapshot: UiSnapshot,
    /// The lenses inside the shared slice (the culled frustum faces).
    pub lenses: Vec<PresentationKind>,
    /// The membrane scope — the backing cell + the culled affordance names. The
    /// recipient rehydrates this PER-VIEWER through the REAL `is_attenuation`.
    pub affordance_scope: AffordanceSnapshot,
    /// The attenuated firmament cap the recipient is granted (the role).
    pub attenuated_cap: Capability,
    /// The rights tier of the attenuated cap (the legible role label).
    pub attenuated_rights: AuthRequired,
    /// The backing cell the artifact re-views (the membrane origin).
    pub backing: CellId,
    /// Whether this artifact has been REVOKED. The membrane re-checks authority at
    /// each reacquisition; a revoked artifact rehydrates NOTHING (member removed).
    pub revoked: bool,
}

impl SharedArtifact {
    /// **Revoke** the artifact — the org-settings "remove member". After revocation
    /// [`Self::rehydrate_for`] yields the empty surface, regardless of caps held:
    /// the right to re-view is withdrawn (revocable between projections).
    pub fn revoke(&mut self) {
        self.revoked = true;
    }

    /// `true` iff the artifact is still live (not revoked).
    pub fn is_live(&self) -> bool {
        !self.revoked
    }

    /// **Rehydrate** the artifact for a recipient holding `recipient_held`, against
    /// the live `surface` (the witness-graph). Returns the affordance names the
    /// recipient ACTUALLY gets — the REAL [`AffordanceSnapshot::rehydrate_for`]
    /// (per-viewer, through `is_attenuation`), CONFINED to the artifact's frustum,
    /// and EMPTY if the artifact was revoked. Two recipients holding different caps
    /// rehydrate DIFFERENT slices from the SAME artifact (the membrane property).
    pub fn rehydrate_for(
        &self,
        surface: &AffordanceSurface,
        recipient_held: &SurfaceCapability,
    ) -> Vec<String> {
        if self.revoked {
            return Vec::new();
        }
        let rehydrated = self.affordance_scope.rehydrate_for(surface, recipient_held);
        let mut names = rehydrated.names();
        names.retain(|n| self.affordance_scope.affordance_names.contains(n));
        names
    }
}

// ===========================================================================
// §4 — a constructor for a recipient cap (used by callers building a preview).
// ===========================================================================

/// Build a recipient-held [`SurfaceCapability`] over `backing` carrying `rights`,
/// bound to `surface` — the cap a recipient presents to rehydrate a shared
/// artifact. Crate-public so the cockpit (and tests) can mint a preview viewer
/// without re-deriving the firmament handle by hand.
pub fn recipient_window_cap(
    surface: SurfaceId,
    backing: CellId,
    rights: Rights,
) -> SurfaceCapability {
    SurfaceCapability::new(
        surface,
        Capability {
            target: Target::Surface { cell: backing },
            rights,
        },
    )
}

// ===========================================================================
// TESTS — the editor model, proven gpui-free against the REAL machinery.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affordance::CellAffordance;
    use crate::presentable::{FocusTarget, PresentationKind};
    use crate::surface::SurfaceId;
    use crate::ui_snapshot::UiSnapshot;
    use crate::world::World;
    use dregg_firmament::AuthRequired as FAuth;
    use dregg_turn::action::Effect;

    /// A backing surface over `backing` declaring a `view` (narrow) + an `admin`
    /// (wide) affordance — the two-tier shape the membrane divides on.
    fn two_tier_surface(backing: CellId) -> AffordanceSurface {
        AffordanceSurface::new(backing)
            .declare(CellAffordance::new(
                "view",
                Requirement::AtLeast(Credential::Signature), // narrow — any signer clears it
                Effect::IncrementNonce { cell: backing },
            ))
            .declare(CellAffordance::new(
                "admin",
                Requirement::AtLeast(Credential::Either), // wide — only a root-ish holder clears it
                Effect::IncrementNonce { cell: backing },
            ))
    }

    /// The operator's held window cap over `backing` carrying `rights`.
    fn held_cap(surface: SurfaceId, backing: CellId, rights: FAuth) -> SurfaceCapability {
        recipient_window_cap(surface, backing, rights)
    }

    /// Open an editor over a fresh world's genesis cell, a wide held cap, and the
    /// two-tier surface.
    fn editor() -> (SnapshotEditor, CellId) {
        let mut w = World::new();
        let backing = w.genesis_cell(0x10, 1_000);
        let snap = UiSnapshot::capture(&w, FocusTarget::Cell(backing), PresentationKind::RawFields);
        let surface = two_tier_surface(backing);
        // The operator holds the WIDE Either cap (the ceiling).
        let held = held_cap(SurfaceId(1), backing, FAuth::Either);
        (SnapshotEditor::open(snap, surface, held), backing)
    }

    // ── the frustum starts FULL and culling NARROWS ─────────────────────────

    #[test]
    fn the_frustum_starts_full_and_culling_only_narrows() {
        let (mut ed, _backing) = editor();
        // Full: every lens + both captured affordances.
        assert_eq!(ed.frustum().lenses().len(), ALL_LENSES.len());
        assert_eq!(ed.frustum().affordance_names(), &["admin", "view"]);

        // Cull a lens OUT → it leaves the slice (narrows).
        assert!(!ed.cull_lens(PresentationKind::Source));
        assert!(!ed.frustum().has_lens(PresentationKind::Source));
        assert_eq!(ed.frustum().lenses().len(), ALL_LENSES.len() - 1);

        // Cull a sub-object OUT → it leaves the slice (narrows).
        assert!(!ed.cull_affordance("admin"));
        assert!(!ed.frustum().has_affordance("admin"));
        assert_eq!(ed.frustum().affordance_names(), &["view"]);

        // Re-toggle restores a CAPTURED member (the ceiling), never a foreign one.
        assert!(ed.cull_affordance("admin"));
        assert!(ed.frustum().has_affordance("admin"));
        // A name that was NEVER captured cannot be added — the cull cannot widen
        // past what was seen.
        assert!(!ed.cull_affordance("forge-a-new-power"));
        assert!(!ed.frustum().has_affordance("forge-a-new-power"));
    }

    // ── the pare dial NARROWS and REFUSES amplification in-band ──────────────

    #[test]
    fn the_pare_dial_narrows_and_refuses_amplification_in_band() {
        let (mut ed, _backing) = editor();
        // Held is Either; paring to Signature is a sound attenuation.
        let out = ed.pare_to("Signature");
        assert!(
            out.is_pared(),
            "Signature ⊆ Either is a sound attenuation: {out:?}"
        );
        assert_eq!(
            out,
            PareOutcome::Pared {
                rights: AuthRequired::Signature
            }
        );
        assert!(
            ed.verify().sound,
            "the pare verifies as a sound attenuation"
        );

        // Now open an editor whose held cap is NARROW (Signature) and try to WIDEN
        // it to Either — the REAL is_attenuation REFUSES it in-band.
        let mut w = World::new();
        let backing = w.genesis_cell(0x20, 0);
        let snap = UiSnapshot::capture(&w, FocusTarget::Cell(backing), PresentationKind::RawFields);
        let surface = two_tier_surface(backing);
        let narrow_held = held_cap(SurfaceId(2), backing, FAuth::Signature);
        let mut narrow_ed = SnapshotEditor::open(snap, surface, narrow_held);

        let widen = narrow_ed.pare_to("Either");
        assert!(
            !widen.is_pared(),
            "Either ⊄ Signature — a widening is REFUSED in-band: {widen:?}"
        );
        match widen {
            PareOutcome::Refused { reason } => assert!(
                reason.contains("AMPLIFY") || reason.to_lowercase().contains("amplif"),
                "the refusal names amplification: {reason}"
            ),
            other => panic!("expected a Refused, got {other:?}"),
        }
        // And the share is REFUSED too (cannot mint an over-wide artifact).
        assert!(
            matches!(narrow_ed.share(), Err(ShareError::WouldAmplify { .. }))
                || matches!(narrow_ed.share(), Err(ShareError::PareIncomplete)),
            "an amplifying pare cannot produce a shared artifact"
        );
    }

    // ── live verification: the membrane-projected preview is the REAL slice ──

    #[test]
    fn verify_shows_the_membrane_projected_recipient_preview() {
        let (mut ed, _backing) = editor();

        // Pare to Signature: a recipient holding only Signature can see `view`
        // (Signature ⊆ Signature) but NOT `admin` (Either ⊄ Signature). The preview
        // is the REAL membrane projection, not a narration.
        assert!(ed.pare_to("Signature").is_pared());
        let v = ed.verify();
        assert!(v.sound);
        assert_eq!(
            v.recipient_affordances,
            vec!["view".to_string()],
            "a Signature recipient rehydrates ONLY the narrow `view` affordance"
        );

        // Pare WIDER (to the held Either): the recipient now also sees `admin`.
        assert!(ed.pare_to("Either").is_pared());
        let v_wide = ed.verify();
        assert_eq!(
            v_wide.recipient_affordances,
            vec!["admin".to_string(), "view".to_string()],
            "an Either recipient rehydrates BOTH affordances"
        );

        // Now CULL `admin` out of the frustum: even the Either recipient no longer
        // sees it (the cull is the tighter boundary than the cap would admit).
        assert!(!ed.cull_affordance("admin"));
        let v_culled = ed.verify();
        assert_eq!(
            v_culled.recipient_affordances,
            vec!["view".to_string()],
            "culling `admin` removes it even though the cap would admit it"
        );
    }

    // ── the shared artifact rehydrates attenuated-DIFFERENTLY per viewer ─────

    #[test]
    fn the_shared_artifact_rehydrates_attenuated_differently_per_viewer() {
        let (mut ed, backing) = editor();
        // Share the WIDE slice (pare to Either, full frustum).
        assert!(ed.pare_to("Either").is_pared());
        let artifact = ed.share().expect("a sound share");
        assert_eq!(artifact.attenuated_rights, AuthRequired::Either);
        assert_eq!(artifact.affordance_scope.affordance_names.len(), 2);

        // The live surface the recipients rehydrate against.
        let surface = two_tier_surface(backing);

        // Recipient A holds a WIDE (Either) cap → rehydrates BOTH affordances.
        let wide = held_cap(SurfaceId(9), backing, FAuth::Either);
        // Recipient B holds a NARROW (Signature) cap → rehydrates ONLY `view`.
        let narrow = held_cap(SurfaceId(9), backing, FAuth::Signature);

        let a = artifact.rehydrate_for(&surface, &wide);
        let b = artifact.rehydrate_for(&surface, &narrow);
        assert_eq!(a, vec!["admin".to_string(), "view".to_string()]);
        assert_eq!(b, vec!["view".to_string()]);
        assert_ne!(
            a, b,
            "the SAME artifact rehydrates differently per viewer (the membrane)"
        );
    }

    // ── revocation withdraws the right to re-view ───────────────────────────

    #[test]
    fn revoking_the_artifact_withdraws_the_right_to_re_view() {
        let (mut ed, backing) = editor();
        assert!(ed.pare_to("Either").is_pared());
        let mut artifact = ed.share().expect("a sound share");
        let surface = two_tier_surface(backing);
        let wide = held_cap(SurfaceId(9), backing, FAuth::Either);

        // Before revocation: the wide recipient rehydrates both.
        assert!(artifact.is_live());
        assert_eq!(artifact.rehydrate_for(&surface, &wide).len(), 2);

        // Revoke → the membrane re-checks and yields NOTHING, regardless of caps.
        artifact.revoke();
        assert!(!artifact.is_live());
        assert!(
            artifact.rehydrate_for(&surface, &wide).is_empty(),
            "a revoked artifact rehydrates nothing — the right was withdrawn"
        );
    }

    // ── the share carries the captured snapshot + the culled scope ──────────

    #[test]
    fn the_share_carries_the_snapshot_and_the_culled_membrane_scope() {
        let (mut ed, backing) = editor();
        // Cull `admin` out and a couple lenses, then pare + share.
        assert!(!ed.cull_affordance("admin"));
        assert!(!ed.cull_lens(PresentationKind::Source));
        assert!(!ed.cull_lens(PresentationKind::Graph));
        assert!(ed.pare_to("Signature").is_pared());
        let artifact = ed.share().expect("a sound share");

        // The snapshot is the captured camera (unchanged).
        assert_eq!(artifact.snapshot.focus, FocusTarget::Cell(backing));
        // The membrane scope is the CULLED set (admin removed).
        assert_eq!(
            artifact.affordance_scope.affordance_names,
            vec!["view".to_string()]
        );
        // The lenses are the culled frustum (Source + Graph removed).
        assert!(!artifact.lenses.contains(&PresentationKind::Source));
        assert!(!artifact.lenses.contains(&PresentationKind::Graph));
        assert!(artifact.lenses.contains(&PresentationKind::RawFields));
        // The cap is the pared (narrow) one.
        assert_eq!(artifact.attenuated_rights, AuthRequired::Signature);
    }

    // ── an incomplete pare refuses the share (fail-closed) ──────────────────

    #[test]
    fn an_incomplete_pare_refuses_the_share() {
        let (ed, _backing) = editor();
        // No pare_to called → the dial is unset → share is fail-closed.
        assert!(!ed.verify().sound, "an unset pare is not sound");
        assert_eq!(ed.share(), Err(ShareError::PareIncomplete));
    }
}
