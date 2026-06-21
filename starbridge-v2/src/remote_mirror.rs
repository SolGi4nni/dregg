//! The REMOTE MIRROR — reflecting a remote dregg image through an attenuated
//! firmament mirror-cap dialed over the netlayer (the §4 frontier of
//! `docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md`).
//!
//! starbridge is a self-hosting reflexive image; its inspector, debugger, and
//! scrubber are dregg objects focusable like any cell. This module extends that
//! reflexivity ACROSS DISTANCE (`n > 1`, the firmament thesis): one image
//! INSPECTS + DEBUGS a *remote* dregg image live, by holding a **mirror-cap**
//! over a remote cell and resolving the remote object's [`Inspectable`]
//! projection through that cap — read-only by default, at exactly the depth the
//! cap authorizes, and **never any authority the cap does not confer**.
//!
//! ## The mirror-cap is a REAL firmament cap (no parallel model)
//!
//! A mirror-cap is a genuine [`dregg_firmament::Capability`] whose target is a
//! [`Target::Distributed`](dregg_firmament::Target::Distributed) cell (the
//! remote thing being reflected), carrying a [`MirrorDepth`] — the reflective
//! attenuation axis (`Structure ⊑ ReadState ⊑ Live`). It introduces no new
//! authority primitive: it reuses the `(target, rights)` handle and the genuine
//! `granted ⊆ held` ([`is_attenuation`](dregg_firmament::is_attenuation)) gate
//! verbatim, and it attenuates on TWO axes that BOTH reduce to a monotone-order
//! check:
//!
//!   * the **rights** axis — the real [`AuthRequired`](dregg_firmament::AuthRequired)
//!     lattice (`Either → Signature → None`), gated by `is_attenuation`. A
//!     read-only mirror is a `Signature`-or-narrower cap; the *write* path
//!     ([`RemoteMirror::propose_edit`]) demands write-class rights the read-only
//!     mirror does not hold, and is refused at the cap fabric — this is
//!     `viewSurface_confers_no_edge` made concrete: **viewing the remote confers
//!     no edge to write it.**
//!   * the **depth** axis — [`MirrorDepth`]: `Live ⊒ ReadState ⊒ Structure`. A
//!     `ReadState` mirror reads remote cell state but cannot follow the live
//!     dynamics stream; a `Structure` mirror sees only shape (id, cap count,
//!     lifecycle flags) with state values redacted. A widen on either axis is
//!     refused identically (`is_attenuation` returns `None` on the rights axis,
//!     [`MirrorDepth::widens_to`] is `false` on the depth axis) — the
//!     no-amplification rule, on the reflection axis.
//!
//! This is §6 Seam 2 ("`MirrorDepth` as a second rights coordinate") realized
//! *adjacent* to the shared `dregg-firmament` crate: the rights coordinate stays
//! the crate's real `AuthRequired` (untouched), the depth coordinate lives here,
//! and a [`MirrorCap`] narrows iff it narrows on BOTH — the product order.
//!
//! ## Distance is honest (the `Bounds` relax, the verbs do not)
//!
//! Every reflection carries the firmament's [`Bounds`](dregg_firmament::Bounds)
//! for the resolution. At `n = 1` (the remote image is, in fact, on this box)
//! the bounds collapse to strong-local ([`Bounds::LOCAL`](dregg_firmament::Bounds::LOCAL));
//! at `n > 1` (over the netlayer) revocation is eventual and commit is
//! quorum-gated ([`Bounds::distributed`](dregg_firmament::Bounds::distributed)).
//! The *verbs* — hold a mirror, reflect, (try to) edit — are unchanged across
//! `n`; only the bounds relax. This is the firmament's `n`-collapse, applied to
//! reflection.
//!
//! ## Headless + transport-abstract
//!
//! The reflection resolves through a [`RemoteImage`] transport trait, so the
//! pure mirror logic is `cargo test`-able with a [`FixtureImage`] (no network,
//! no gpui). The production binding is the live HTTP/SSE node connection
//! ([`crate::live_node::LiveNode`] / [`crate::live_node::LiveReflection`]) — the
//! transport feeds the SAME `CellListEntry → Inspectable` projection the local
//! inspector already renders, so a remote mirrored cell renders identically to a
//! local one (no parallel view path).
//!
//! gpui-free. Compiles + tests under `embedded-executor` (which already pulls
//! `dregg-firmament`).

use dregg_firmament::{is_attenuation, AuthRequired, Backing, Bounds, Capability, Target};
use dregg_types::CellId;

use crate::live_node::LiveReflection;
use crate::model::CellListEntry;
use crate::reflect::Inspectable;

// ===========================================================================
// MIRROR DEPTH — the reflective attenuation axis (the second rights coordinate)
// ===========================================================================

/// The reflective-depth lattice: `Structure ⊑ ReadState ⊑ Live`.
///
/// This is the depth coordinate of the mirror-cap's `(AuthRequired × MirrorDepth)`
/// rights (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §1.2/§6 Seam 2). It is a total
/// order; narrowing is moving DOWN it, and a widen is refused exactly as a
/// rights widen is. Lives here (not in the shared `dregg-firmament` crate)
/// deliberately: the crate's rights stay the untouched real `AuthRequired`; the
/// product order is composed at the [`MirrorCap`] boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MirrorDepth {
    /// See only SHAPE — the cell id, cap count, lifecycle flags — with state
    /// VALUES (balance, nonce, program contents) redacted. The least-trusted
    /// mirror: "show me the wiring without the secrets" (a remote auditor).
    Structure,
    /// See the live STATE — balances, nonces, program presence — but NOT the
    /// dynamics tail. The debugger's default lens.
    ReadState,
    /// Follow the live DYNAMICS stream as the remote image evolves. The only
    /// depth that observes liveness; granted sparingly.
    Live,
}

impl MirrorDepth {
    /// Is `self` at most as deep as `held`? (the narrowing check on the depth
    /// axis — `granted ⊑ held`). The depth analogue of
    /// [`is_attenuation`](dregg_firmament::is_attenuation).
    pub fn is_at_most(self, held: MirrorDepth) -> bool {
        self <= held
    }

    /// Would moving from `self` to `target` be a WIDEN (a forbidden
    /// amplification)? `true` iff `target` is strictly deeper than `self`. The
    /// no-amplification tooth on the reflection axis.
    pub fn widens_to(self, target: MirrorDepth) -> bool {
        target > self
    }

    /// Does this depth authorize reading the cell's STATE values? `Structure`
    /// redacts state; `ReadState`/`Live` reveal it.
    pub fn reveals_state(self) -> bool {
        self >= MirrorDepth::ReadState
    }

    /// Does this depth authorize following the live DYNAMICS stream? Only `Live`.
    pub fn reveals_dynamics(self) -> bool {
        self == MirrorDepth::Live
    }
}

// ===========================================================================
// MIRROR CAP — a real firmament cap (over a remote cell) + a reflective depth
// ===========================================================================

/// A **mirror-cap**: the authority to REFLECT over a remote cell, at a bounded
/// depth, read-only unless explicitly write-class.
///
/// It is a real [`dregg_firmament::Capability`] over a
/// [`Target::Distributed`](dregg_firmament::Target::Distributed) cell, paired
/// with a [`MirrorDepth`]. The two coordinates compose the product rights
/// `(AuthRequired × MirrorDepth)`; [`MirrorCap::attenuate`] narrows on EITHER and
/// refuses a widen on BOTH through the genuine gates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MirrorCap {
    /// The REAL firmament cap — `target = Distributed{cell}`, rights on the genuine
    /// [`AuthRequired`] lattice.
    cap: Capability,
    /// The reflective depth this mirror authorizes.
    depth: MirrorDepth,
}

impl MirrorCap {
    /// Mint a mirror-cap over a remote `cell` with `rights` (the read/write
    /// authority) at `depth` (the reflective extent). The minter is the holder of
    /// the underlying authority over the cell — a mirror you do not hold cannot be
    /// faked into existence.
    pub fn new(cell: CellId, rights: AuthRequired, depth: MirrorDepth) -> Self {
        MirrorCap {
            cap: Capability::distributed(cell, rights),
            depth,
        }
    }

    /// A **read-only mirror** at `depth`: `rights = Signature` (the read-floor —
    /// satisfiable by a signature, NOT amplifiable to the `Either` write tier).
    /// The debugger's default mirror.
    pub fn read_only(cell: CellId, depth: MirrorDepth) -> Self {
        MirrorCap::new(cell, AuthRequired::Signature, depth)
    }

    /// A **structure-only mirror**: read-only AND `depth = Structure` — shape
    /// without state. The least-trusted mirror handed to a remote auditor.
    pub fn structure_only(cell: CellId) -> Self {
        MirrorCap::read_only(cell, MirrorDepth::Structure)
    }

    /// The remote cell this mirror reflects.
    pub fn cell(&self) -> Option<CellId> {
        match &self.cap.target {
            Target::Distributed { cell } => Some(*cell),
            // A mirror-cap is always over a distributed (remote) cell; other
            // targets are not mirrors.
            _ => None,
        }
    }

    /// The reflective depth this mirror authorizes.
    pub fn depth(&self) -> MirrorDepth {
        self.depth
    }

    /// The rights this mirror holds over the remote cell.
    pub fn rights(&self) -> &AuthRequired {
        &self.cap.rights
    }

    /// Does this mirror authorize READING (reflecting) the remote cell at all? A
    /// reflection needs *some* read authority — a non-`Impossible`,
    /// non-`None`-only cap whose depth reveals at least structure. (`Structure`
    /// depth still reflects shape; the floor is "the cap is satisfiable".)
    pub fn can_reflect(&self) -> bool {
        // `Impossible` authorizes nothing; everything else (Signature/Proof/
        // Either/None/Custom) is a holdable read floor for reflection.
        !matches!(self.cap.rights, AuthRequired::Impossible)
    }

    /// Does this mirror authorize WRITING (proposing an edit) to the remote cell?
    /// A write demands a write-class right — `Either` (signature OR proof
    /// suffices to author a turn). A read-only (`Signature`-narrowed) mirror does
    /// NOT hold it: **viewing confers no edge to edit** (`viewSurface_confers_no_edge`).
    pub fn can_edit(&self) -> bool {
        // The write tier is `Either` (the cell's own `send`/`set_state` floor is
        // `Signature`, but a *mirror* deliberately treats the writable authority
        // as the wider `Either` so a read-only `Signature` mirror is strictly
        // weaker — the read/write split the design requires). A mirror can write
        // iff it could itself have been attenuated FROM an `Either` write cap and
        // still holds the `Either` tier.
        is_attenuation(&self.cap.rights, &AuthRequired::Either)
            && is_attenuation(&AuthRequired::Either, &self.cap.rights)
    }

    /// Attenuate this mirror on BOTH coordinates — `narrower` rights (gated by the
    /// real [`is_attenuation`]) AND `shallower` depth (gated by the depth order).
    /// Returns `None` if EITHER would be a widen (the product-order meet).
    ///
    /// This is the heart of "adoption is attenuation" on the reflection axis: a
    /// remote operator is handed a mirror they cannot amplify. A `Live` mirror
    /// narrows to `ReadState`/`Structure`; a `Structure` mirror REFUSES to widen
    /// to `ReadState`; a `Signature` (read-only) mirror REFUSES to widen to
    /// `Either` (write).
    pub fn attenuate(&self, narrower: AuthRequired, shallower: MirrorDepth) -> Option<MirrorCap> {
        // Rights axis: the genuine firmament gate (`granted ⊆ held`).
        let cap = self.cap.attenuate(narrower)?;
        // Depth axis: narrowing is moving DOWN the depth lattice.
        if !shallower.is_at_most(self.depth) {
            return None;
        }
        Some(MirrorCap { cap, depth: shallower })
    }
}

// ===========================================================================
// REMOTE IMAGE — the transport the mirror dials over (abstract; the netlayer)
// ===========================================================================

/// What the mirror needs from the remote image's transport: fetch the remote
/// cell's wire snapshot. This is the netlayer seam — the mirror-cap "dialed over
/// the netlayer" resolves the remote object through THIS trait.
///
/// A [`FixtureImage`] implements it from an in-memory map (the `cargo test`
/// binding, no network); the production binding is the live HTTP/SSE node
/// connection ([`crate::live_node::LiveNode`]), which fetches `GET /api/cells`
/// and projects the entry through [`LiveReflection`]. The pure mirror logic
/// never knows which transport it holds — exactly the firmament's
/// backing-agnostic [`Router`](dregg_firmament::Router) discipline.
pub trait RemoteImage {
    /// The distance `n` to this remote image (machines spread across). `1` ⇒ the
    /// remote is, in fact, on this box (the `n = 1` collapse); `> 1` ⇒ over the
    /// netlayer. Drives the [`Bounds`] the reflection carries.
    fn distance(&self) -> u32;

    /// Fetch the remote cell's wire snapshot, or `None` if the remote image has no
    /// such cell. This is the ONLY authority the transport itself confers — the
    /// raw bytes; the mirror-cap is what gates whether (and at what depth) the
    /// holder may *see* them.
    fn fetch_cell(&self, cell: CellId) -> Option<CellListEntry>;
}

/// An in-memory remote image for tests: a fixed map of `cell → wire entry` at a
/// fixed distance. The `cargo test` binding of [`RemoteImage`] — no network.
#[derive(Clone, Debug, Default)]
pub struct FixtureImage {
    distance: u32,
    cells: Vec<(CellId, CellListEntry)>,
}

impl FixtureImage {
    /// A fixture image at distance `n` (the simulated number of machines).
    pub fn new(distance: u32) -> Self {
        FixtureImage { distance, cells: Vec::new() }
    }

    /// Add a remote cell's wire snapshot to this fixture image.
    pub fn with_cell(mut self, cell: CellId, entry: CellListEntry) -> Self {
        self.cells.push((cell, entry));
        self
    }
}

impl RemoteImage for FixtureImage {
    fn distance(&self) -> u32 {
        self.distance
    }

    fn fetch_cell(&self, cell: CellId) -> Option<CellListEntry> {
        self.cells
            .iter()
            .find(|(c, _)| *c == cell)
            .map(|(_, e)| e.clone())
    }
}

// ===========================================================================
// THE REFLECTION — what a mirror yields (a projection + the honest bounds)
// ===========================================================================

/// The result of reflecting a remote cell through a mirror-cap: the projected
/// [`Inspectable`], the depth it was projected AT, and the firmament [`Bounds`]
/// that held (the honest distance bounds). The depth-redaction is already baked
/// into the `Inspectable` (a `Structure` reflection carries no state fields).
#[derive(Clone, Debug)]
pub struct RemoteReflection {
    /// The depth this reflection was resolved at (the mirror's authorized depth).
    pub depth: MirrorDepth,
    /// The firmament bounds that held — relaxed honestly with distance.
    pub bounds: Bounds,
    /// Which backing resolved it (always the distributed/net path for a remote
    /// mirror; carried so the reflection is symmetric with a local resolution).
    pub backing: Backing,
    /// The projected remote object, redacted to the mirror's depth.
    pub view: Inspectable,
}

/// Why a reflection or edit through a mirror was REFUSED — surfaced honestly,
/// never faked into a successful-looking projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MirrorRefusal {
    /// The mirror-cap does not authorize reflection at all (`Impossible` rights).
    NoReflectAuthority,
    /// The mirror is not over a remote (distributed) cell — not a mirror.
    NotARemoteCell,
    /// The remote image has no such cell (a dangling remote focus).
    RemoteCellAbsent,
    /// The edit was refused: the mirror holds no write-class authority over the
    /// remote cell (`viewSurface_confers_no_edge` — a read-only mirror cannot
    /// write). Carries the rights the mirror DID hold, for the honest log.
    EditUnauthorized { held: AuthRequired },
}

/// THE REMOTE MIRROR — a mirror-cap pointed at a [`RemoteImage`] transport. The
/// reflexive image reaching across distance: it holds the cap, dials the
/// transport, and yields the remote object's projection at exactly the depth (and
/// with exactly the authority) the cap confers.
pub struct RemoteMirror<'t, T: RemoteImage> {
    cap: MirrorCap,
    transport: &'t T,
}

impl<'t, T: RemoteImage> RemoteMirror<'t, T> {
    /// Aim a mirror-cap at a remote-image transport.
    pub fn new(cap: MirrorCap, transport: &'t T) -> Self {
        RemoteMirror { cap, transport }
    }

    /// The mirror-cap this mirror holds.
    pub fn cap(&self) -> &MirrorCap {
        &self.cap
    }

    /// The firmament bounds for a resolution at this transport's distance — the
    /// honest `n`-relaxation (`n = 1` ⇒ strong-local; `n > 1` ⇒ eventual/quorum).
    pub fn bounds(&self) -> Bounds {
        Bounds::distributed(self.transport.distance())
    }

    /// **REFLECT** the remote cell through the mirror — the read face.
    ///
    /// Resolves the remote object's [`Inspectable`] at the cap's depth, redacting
    /// state for a `Structure` mirror, and carries the honest [`Bounds`]. Refuses
    /// (returns `Err`) if the mirror has no reflect authority, is not over a
    /// remote cell, or the remote image has no such cell — never a faked
    /// projection.
    pub fn reflect(&self) -> Result<RemoteReflection, MirrorRefusal> {
        if !self.cap.can_reflect() {
            return Err(MirrorRefusal::NoReflectAuthority);
        }
        let cell = self.cap.cell().ok_or(MirrorRefusal::NotARemoteCell)?;
        let entry = self
            .transport
            .fetch_cell(cell)
            .ok_or(MirrorRefusal::RemoteCellAbsent)?;

        // Project through the SAME live-node reflection the local inspector uses,
        // then REDACT to the mirror's depth. A `Structure` mirror sees shape only;
        // `ReadState`/`Live` see state.
        let full = LiveReflection::reflect_cell_entry(&entry);
        let view = redact_to_depth(full, self.cap.depth);

        Ok(RemoteReflection {
            depth: self.cap.depth,
            bounds: self.bounds(),
            backing: Backing::DistributedTurn,
            view,
        })
    }

    /// **PROPOSE AN EDIT** to the remote cell through the mirror — the write face,
    /// gated.
    ///
    /// A write demands a write-class mirror ([`MirrorCap::can_edit`]); a read-only
    /// mirror is REFUSED at the cap fabric with [`MirrorRefusal::EditUnauthorized`]
    /// — the `viewSurface_confers_no_edge` tooth: holding a view (mirror) over the
    /// remote confers NO edge to write it. (The authorized path returns the cell
    /// the edit would target; actually submitting the edit is a turn over the net,
    /// the §4.2 `resume`/delegated-turn path, out of this read-mirror's scope.)
    pub fn propose_edit(&self) -> Result<CellId, MirrorRefusal> {
        if !self.cap.can_edit() {
            return Err(MirrorRefusal::EditUnauthorized {
                held: self.cap.rights().clone(),
            });
        }
        self.cap.cell().ok_or(MirrorRefusal::NotARemoteCell)
    }
}

/// Redact an [`Inspectable`] to a [`MirrorDepth`]: a `Structure` mirror keeps only
/// SHAPE fields (id, cap count, lifecycle/presence flags) and drops STATE values
/// (balance, nonce). `ReadState`/`Live` keep everything. The depth-attenuation
/// made concrete on the projection.
fn redact_to_depth(mut view: Inspectable, depth: MirrorDepth) -> Inspectable {
    if depth.reveals_state() {
        // ReadState / Live: full projection.
        return view;
    }
    // Structure: keep shape, redact state values. Balance/nonce are STATE; id,
    // capability count, and the has_* / found flags are SHAPE.
    view.fields.retain(|f| {
        !matches!(f.key.as_str(), "balance" | "nonce")
    });
    view.subtitle = format!("structure-only mirror · {} caps", structure_caps(&view));
    view
}

/// The cap count read off a (possibly redacted) projection's `capabilities`
/// field, for the structure-mirror subtitle. `0` if absent.
fn structure_caps(view: &Inspectable) -> u64 {
    view.fields
        .iter()
        .find(|f| f.key == "capabilities")
        .and_then(|f| match &f.value {
            crate::reflect::FieldValue::Count(n) => Some(*n),
            _ => None,
        })
        .unwrap_or(0)
}

// ===========================================================================
// TESTS — both polarities (the mirror reflects ✓ / cannot exceed its rights ✗)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn entry(id: CellId, balance: i64, nonce: u64, caps: usize) -> CellListEntry {
        CellListEntry {
            id: dregg_types::hex_encode(id.as_bytes()),
            balance,
            nonce,
            capability_count: caps,
            has_delegate: false,
            has_program: true,
            found: true,
        }
    }

    fn field<'a>(view: &'a Inspectable, key: &str) -> Option<&'a crate::reflect::Field> {
        view.fields.iter().find(|f| f.key == key)
    }

    // ---- POLARITY ✓ : a read-mirror reflects the remote cell's state ----------

    #[test]
    fn read_mirror_reflects_remote_state() {
        let cell = cid(7);
        let img = FixtureImage::new(5).with_cell(cell, entry(cell, 1234, 9, 3));
        let mirror = RemoteMirror::new(MirrorCap::read_only(cell, MirrorDepth::ReadState), &img);

        let r = mirror.reflect().expect("a read mirror reflects the remote cell");
        assert_eq!(r.depth, MirrorDepth::ReadState);
        assert_eq!(r.backing, Backing::DistributedTurn);

        // ReadState reveals STATE: balance + nonce are present and correct.
        match field(&r.view, "balance").map(|f| &f.value) {
            Some(crate::reflect::FieldValue::Balance(b)) => assert_eq!(*b, 1234),
            other => panic!("expected balance 1234, got {other:?}"),
        }
        match field(&r.view, "nonce").map(|f| &f.value) {
            Some(crate::reflect::FieldValue::Count(n)) => assert_eq!(*n, 9),
            other => panic!("expected nonce 9, got {other:?}"),
        }
    }

    #[test]
    fn distance_relaxes_bounds_honestly_but_n1_collapses() {
        let cell = cid(1);
        // n > 1 over the netlayer: eventual revoke, quorum commit.
        let far = FixtureImage::new(5).with_cell(cell, entry(cell, 0, 0, 0));
        let m_far = RemoteMirror::new(MirrorCap::read_only(cell, MirrorDepth::ReadState), &far);
        let b = m_far.reflect().unwrap().bounds;
        assert_eq!(b.n, 5);
        assert!(!b.revocation_immediate);
        assert!(!b.commit_synchronous);

        // n = 1 collapse: a "remote" image that is in fact on this box is strong-local.
        let near = FixtureImage::new(1).with_cell(cell, entry(cell, 0, 0, 0));
        let m_near = RemoteMirror::new(MirrorCap::read_only(cell, MirrorDepth::ReadState), &near);
        let bl = m_near.reflect().unwrap().bounds;
        assert_eq!(bl, Bounds::LOCAL);
        assert!(bl.revocation_immediate && bl.commit_synchronous);
    }

    // ---- POLARITY ✗ : the mirror cannot exceed its attenuated rights ----------

    #[test]
    fn read_mirror_cannot_write_view_confers_no_edge() {
        let cell = cid(7);
        let img = FixtureImage::new(5).with_cell(cell, entry(cell, 1234, 9, 3));
        // A read-only (Signature) mirror.
        let mirror = RemoteMirror::new(MirrorCap::read_only(cell, MirrorDepth::ReadState), &img);

        // It can reflect (read) ...
        assert!(mirror.reflect().is_ok());
        // ... but proposing an edit is REFUSED — the view confers no edge.
        match mirror.propose_edit() {
            Err(MirrorRefusal::EditUnauthorized { held }) => {
                assert_eq!(held, AuthRequired::Signature);
            }
            other => panic!("a read-only mirror must NOT authorize an edit, got {other:?}"),
        }
    }

    #[test]
    fn write_mirror_can_propose_edit() {
        let cell = cid(7);
        let img = FixtureImage::new(1).with_cell(cell, entry(cell, 1234, 9, 3));
        // A write-class (Either) mirror.
        let mirror =
            RemoteMirror::new(MirrorCap::new(cell, AuthRequired::Either, MirrorDepth::Live), &img);
        assert_eq!(mirror.propose_edit(), Ok(cell));
    }

    #[test]
    fn structure_mirror_redacts_state() {
        let cell = cid(7);
        let img = FixtureImage::new(5).with_cell(cell, entry(cell, 999, 4, 2));
        let mirror = RemoteMirror::new(MirrorCap::structure_only(cell), &img);

        let r = mirror.reflect().expect("a structure mirror still reflects shape");
        assert_eq!(r.depth, MirrorDepth::Structure);
        // STATE is redacted: no balance, no nonce.
        assert!(field(&r.view, "balance").is_none(), "structure mirror must redact balance");
        assert!(field(&r.view, "nonce").is_none(), "structure mirror must redact nonce");
        // SHAPE survives: id + capability count are present.
        assert!(field(&r.view, "id").is_some());
        match field(&r.view, "capabilities").map(|f| &f.value) {
            Some(crate::reflect::FieldValue::Count(n)) => assert_eq!(*n, 2),
            other => panic!("structure mirror keeps cap count, got {other:?}"),
        }
    }

    // ---- the attenuation lattice: narrow on both axes, refuse every widen -----

    #[test]
    fn attenuate_narrows_both_axes() {
        let cell = cid(3);
        // A Live, Either (full) mirror.
        let full = MirrorCap::new(cell, AuthRequired::Either, MirrorDepth::Live);

        // Narrow rights Either -> Signature AND depth Live -> ReadState: allowed.
        let narrowed = full
            .attenuate(AuthRequired::Signature, MirrorDepth::ReadState)
            .expect("narrowing both axes is a genuine attenuation");
        assert_eq!(narrowed.rights(), &AuthRequired::Signature);
        assert_eq!(narrowed.depth(), MirrorDepth::ReadState);
        assert!(!narrowed.can_edit(), "a Signature mirror is read-only");
    }

    #[test]
    fn attenuate_refuses_rights_widen() {
        let cell = cid(3);
        // A read-only Signature mirror cannot widen to Either (write).
        let ro = MirrorCap::read_only(cell, MirrorDepth::ReadState);
        assert!(
            ro.attenuate(AuthRequired::Either, MirrorDepth::ReadState).is_none(),
            "widening Signature -> Either (read -> write) must be refused"
        );
    }

    #[test]
    fn attenuate_refuses_depth_widen() {
        let cell = cid(3);
        // A Structure mirror cannot widen to ReadState (shape -> state).
        let structure = MirrorCap::structure_only(cell);
        assert!(
            structure.attenuate(AuthRequired::Signature, MirrorDepth::ReadState).is_none(),
            "widening Structure -> ReadState (shape -> state) must be refused"
        );
        // ... and certainly not to Live.
        assert!(structure
            .attenuate(AuthRequired::Signature, MirrorDepth::Live)
            .is_none());
    }

    #[test]
    fn depth_lattice_order_and_amplification_tooth() {
        // The total order Structure ⊑ ReadState ⊑ Live.
        assert!(MirrorDepth::Structure.is_at_most(MirrorDepth::ReadState));
        assert!(MirrorDepth::ReadState.is_at_most(MirrorDepth::Live));
        assert!(MirrorDepth::Structure.is_at_most(MirrorDepth::Live));
        // The no-amplification tooth: a widen is detected on the depth axis.
        assert!(MirrorDepth::Structure.widens_to(MirrorDepth::ReadState));
        assert!(MirrorDepth::ReadState.widens_to(MirrorDepth::Live));
        assert!(!MirrorDepth::Live.widens_to(MirrorDepth::ReadState));
        // Depth capabilities.
        assert!(!MirrorDepth::Structure.reveals_state());
        assert!(MirrorDepth::ReadState.reveals_state());
        assert!(MirrorDepth::Live.reveals_dynamics());
        assert!(!MirrorDepth::ReadState.reveals_dynamics());
    }

    #[test]
    fn impossible_mirror_cannot_reflect() {
        let cell = cid(9);
        let img = FixtureImage::new(1).with_cell(cell, entry(cell, 0, 0, 0));
        let mirror =
            RemoteMirror::new(MirrorCap::new(cell, AuthRequired::Impossible, MirrorDepth::ReadState), &img);
        assert_eq!(mirror.reflect().unwrap_err(), MirrorRefusal::NoReflectAuthority);
    }

    #[test]
    fn absent_remote_cell_is_surfaced_not_faked() {
        let cell = cid(7);
        let other = cid(8);
        // The image has `other`, not `cell`.
        let img = FixtureImage::new(3).with_cell(other, entry(other, 1, 1, 1));
        let mirror = RemoteMirror::new(MirrorCap::read_only(cell, MirrorDepth::ReadState), &img);
        assert_eq!(mirror.reflect().unwrap_err(), MirrorRefusal::RemoteCellAbsent);
    }
}
