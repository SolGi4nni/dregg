//! THE EDITOR / BUFFER SURFACE — a text buffer as a cap-confined Surface cell.
//!
//! The first DEVELOPER content surface of the dregg IDE (A1, the rung after the
//! A0 compositor + agent-activity surface). An editor buffer is exactly the
//! `docs/DREGG-DESKTOP-OS.md` §1 story applied to *text you author*: a window is
//! a `Capability{ Surface(cell) }`, and a buffer is a cap-confined VIEW of a
//! cell whose state IS the buffer — so *who may edit it* is an ocap question the
//! verified executor answers, not an ambient one.
//!
//! **The buffer is backed by a REAL cell.** Its content lives in a gpui-free
//! in-memory document (the visible text), but the AUTHORITY + PROVENANCE of an
//! edit are grounded in the embedded verified [`World`](crate::world): the
//! backing cell carries the buffer's **content digest** (a state field) + a
//! monotonic **revision** (the cell's nonce, advanced by each edit). Committing
//! an edit is a CAP-GATED TURN — a real `Effect::SetField` writing the new
//! digest into the backing cell through [`World::commit_turn`] (the same
//! `TurnExecutor` every other dregg effect runs). So an edit lands iff the
//! editor holds the write authority, and every landed edit appends a real
//! receipt to the world's provenance log. The text is the surface's *content*;
//! the digest-in-the-cell is the authenticated bind a light client can check
//! (the §5 `sourceStateRoot` story, for a buffer).
//!
//! **A read-only buffer is an ATTENUATED cap.** Mirroring the A0 §7 surface
//! discipline (`crate::surface` — a window is owned via the real firmament
//! [`Capability`](dregg_firmament::Capability), ops gated on
//! [`is_attenuation`](dregg_firmament::is_attenuation)), a writable buffer holds
//! a full-rights surface cap and a read-only mirror holds a *narrowed*
//! (`AuthRequired::Signature`) one — obtained only by genuine attenuation, never
//! by self-promotion. A write to a read-only buffer is REFUSED by the SAME
//! `granted ⊆ held` gate the compositor + the firmament use, BEFORE any turn is
//! attempted: the no-amplification rule firing at the editor.
//!
//! Two gates compose, exactly as in [`crate::shell::Shell::present`]:
//!   1. THE BUFFER-CAP GATE — the edit must present a cap that authorizes a
//!      WRITE (a read-only mirror has nothing to present → refused).
//!   2. THE EXECUTOR GATE — the `SetField` turn runs through the real executor
//!      (which enforces the cell's `Permissions` + the whole-turn guarantees).
//!
//! This module is gpui-FREE and `cargo test`-able (the buffer model is built
//! purely from the `World` + a [`SurfaceCapability`]). The cockpit maps
//! [`BufferView`] onto a simple gpui text panel (the IDE's editor pane).

use dregg_cell::{AuthRequired, CellId, FieldElement};

use crate::surface::SurfaceCapability;
use crate::world::{self, World};

/// The state slot the backing cell carries the buffer's content digest in. A
/// fixed, low slot (the cell's `fields[BUFFER_DIGEST_SLOT]`) so the digest rides
/// the cell's authenticated state — an edit that advances the buffer advances
/// the cell's `source_state_root` (the §5 bind), exactly like a balance move.
pub const BUFFER_DIGEST_SLOT: usize = 1;

/// Why a buffer edit was REFUSED. Each variant is a tooth of the buffer's ocap
/// discipline firing — a refusal changes NOTHING (fail-closed, the Lean
/// `present_*_rejected` polarity), surfaced so the operator sees WHY.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BufferError {
    /// **THE READ-ONLY TOOTH** — the editing cap does not authorize a write (it
    /// is a read-only mirror: an attenuated surface cap whose rights are not the
    /// full write authority). The no-amplification rule at the editor: a
    /// read-only buffer cannot promote itself to writable. Carries the rights
    /// the cap actually holds (for the operator log).
    ReadOnly { held: &'static str },
    /// The presented cap does not authorize THIS buffer (its surface id ≠ the
    /// buffer's surface, i.e. cap confusion — a cap for another window cannot
    /// drive this buffer).
    WrongSurface,
    /// The backing cell is gone from the ledger (a dangling buffer — the editor
    /// tells the truth rather than letting it masquerade as live).
    Unbacked,
    /// The edit's `SetField` turn was REJECTED by the real executor (its
    /// `Permissions` or a whole-turn guarantee fired). Carries the executor's
    /// reason. (Distinct from `ReadOnly`, which is the SURFACE-cap gate refusing
    /// before any turn runs.)
    ExecutorRejected(String),
}

impl BufferError {
    /// A short operator-legible label (the tooth that bit).
    pub fn tooth(&self) -> &'static str {
        match self {
            BufferError::ReadOnly { .. } => "read-only",
            BufferError::WrongSurface => "wrong surface",
            BufferError::Unbacked => "unbacked",
            BufferError::ExecutorRejected(_) => "executor-rejected",
        }
    }

    /// A one-line human explanation (the cockpit surfaces this as the refusal
    /// reason — the anti-amplification tooth, surfaced).
    pub fn explain(&self) -> String {
        match self {
            BufferError::ReadOnly { held } => format!(
                "edit REFUSED — this is a READ-ONLY buffer (the cap holds `{held}`, not write \
                 authority); a read-only mirror cannot promote itself (granted ⊆ held)"
            ),
            BufferError::WrongSurface => {
                "edit REFUSED — the presented cap does not authorize this buffer (cap confusion)"
                    .to_string()
            }
            BufferError::Unbacked => {
                "edit REFUSED — the buffer's backing cell is gone from the ledger (dangling)"
                    .to_string()
            }
            BufferError::ExecutorRejected(why) => {
                format!("edit REFUSED by the executor — {why}")
            }
        }
    }
}

/// The gpui-free buffer DOCUMENT — the visible text + its cursor. Plain data so
/// the model stays renderer-agnostic; the cockpit maps it onto a gpui text view.
/// The document is the surface's *content*; its authenticated digest lives in
/// the backing cell (advanced by a committed edit), so the document cannot
/// silently diverge from what the executor witnessed.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BufferDoc {
    /// The buffer text (the lines the editor shows). One `String`; the view
    /// splits on `\n`. (A rope is an optimization the model doesn't need yet.)
    text: String,
    /// The cursor's byte offset into `text` (clamped to `0..=text.len()`).
    cursor: usize,
}

impl BufferDoc {
    /// A fresh empty document.
    pub fn new() -> Self {
        BufferDoc::default()
    }

    /// A document seeded with `text` (cursor at the end).
    pub fn from_text(text: impl Into<String>) -> Self {
        let text = text.into();
        let cursor = text.len();
        BufferDoc { text, cursor }
    }

    /// The buffer text.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// The cursor's byte offset.
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    /// The number of lines (at least 1).
    pub fn line_count(&self) -> usize {
        self.text.split('\n').count()
    }

    /// The lines (for rendering).
    pub fn lines(&self) -> impl Iterator<Item = &str> {
        self.text.split('\n')
    }

    /// THE CONTENT DIGEST — the authenticated projection of the buffer text the
    /// backing cell carries. A deterministic 32-byte commitment (BLAKE3 over the
    /// text), so a different buffer ⇒ a different digest ⇒ a different cell
    /// `source_state_root` (the §5 bind for a buffer). The real compositor would
    /// commit this via Poseidon2; the DISCIPLINE — the cell state binds the
    /// content — is what matters, not the hash choice.
    pub fn digest(&self) -> FieldElement {
        *blake3::hash(self.text.as_bytes()).as_bytes()
    }

    /// A short hex of the digest (operator-legible — the buffer's current
    /// authenticated content id).
    pub fn digest_short(&self) -> String {
        crate::reflect::short_hex(&self.digest())
    }

    // --- gpui-free editing primitives (mutate the IN-MEMORY doc only) --------
    //
    // These change the visible text; they do NOT touch the ledger. The
    // authenticated commit is a SEPARATE, cap-gated act ([`BufferCell::commit`])
    // — editing the view is free, but landing it on-ledger requires the cap.

    /// Insert `s` at the cursor (advancing the cursor past it).
    pub fn insert(&mut self, s: &str) {
        let at = self.cursor.min(self.text.len());
        self.text.insert_str(at, s);
        self.cursor = at + s.len();
    }

    /// Delete the byte before the cursor (backspace); no-op at the start.
    pub fn backspace(&mut self) {
        if self.cursor == 0 || self.text.is_empty() {
            return;
        }
        // Step back to a char boundary (handles multi-byte UTF-8).
        let mut at = self.cursor.min(self.text.len());
        let mut prev = at - 1;
        while prev > 0 && !self.text.is_char_boundary(prev) {
            prev -= 1;
        }
        self.text.replace_range(prev..at, "");
        at = prev;
        self.cursor = at;
    }

    /// Replace the WHOLE buffer text (cursor to the end). The "set contents" op.
    pub fn set_text(&mut self, text: impl Into<String>) {
        self.text = text.into();
        self.cursor = self.text.len();
    }
}

/// THE EDITOR / BUFFER SURFACE — a text buffer as a cap-confined Surface cell.
///
/// Binds a [`SurfaceId`](crate::surface::SurfaceId) (the buffer's window handle
/// in the shell) + the backing cell whose state carries the buffer's digest +
/// the in-memory [`BufferDoc`]. The editing AUTHORITY is the
/// [`SurfaceCapability`] the holder presents: a writable buffer holds the full
/// surface cap; a read-only buffer holds an attenuated one. The cockpit
/// composites it like any other surface; the panel body renders the document.
///
/// This is distinct from a plain cell-view ([`crate::surface::SurfaceKind::CellView`]):
/// a buffer surface's body is editable TEXT whose digest is bound into the
/// backing cell by a verified turn — the §7 cap model carried to authoring.
#[derive(Clone, Debug)]
pub struct BufferCell {
    /// The shell surface id this buffer renders into (its window handle).
    surface: crate::surface::SurfaceId,
    /// The backing cell whose state holds the buffer's content digest (slot
    /// [`BUFFER_DIGEST_SLOT`]) + whose nonce is the buffer's revision. The REAL
    /// anchor in the live ledger.
    backing: CellId,
    /// The visible buffer document (the surface's content).
    doc: BufferDoc,
    /// An operator-facing buffer name (the editor tab title). The TRUSTED-PATH
    /// identity is the backing cell id, drawn by the shell — this is just a label.
    name: String,
}

impl BufferCell {
    /// Open a fresh buffer over `backing` (the cell whose state will carry the
    /// digest), rendering into shell surface `surface`, seeded with `text`.
    pub fn new(
        surface: crate::surface::SurfaceId,
        backing: CellId,
        name: impl Into<String>,
        text: impl Into<String>,
    ) -> Self {
        BufferCell {
            surface,
            backing,
            doc: BufferDoc::from_text(text),
            name: name.into(),
        }
    }

    /// The shell surface id (window handle).
    pub fn surface(&self) -> crate::surface::SurfaceId {
        self.surface
    }

    /// The backing cell id (the authenticated anchor).
    pub fn backing(&self) -> CellId {
        self.backing
    }

    /// The buffer name (editor tab title).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The visible document (read-only borrow — the cockpit renders this).
    pub fn doc(&self) -> &BufferDoc {
        &self.doc
    }

    /// A MUTABLE borrow of the document for free, in-memory editing (typing into
    /// the view). This does NOT touch the ledger — see [`Self::commit`] for the
    /// authenticated, cap-gated landing of an edit.
    pub fn doc_mut(&mut self) -> &mut BufferDoc {
        &mut self.doc
    }

    /// Whether `cap` authorizes a WRITE to this buffer. Mirrors the A0 §7
    /// discipline: the cap must name THIS buffer's surface (anti cap-confusion)
    /// AND carry the FULL write authority (`AuthRequired::None`) — a read-only
    /// mirror (`Signature`/`Proof`/`Either`/`Impossible`) does not. This is the
    /// `granted ⊆ held` direction the firmament + compositor use, on the editor.
    pub fn cap_can_write(&self, cap: &SurfaceCapability) -> bool {
        cap.surface() == self.surface && is_write_rights(cap.rights())
    }

    /// Whether the buffer is read-only UNDER `cap` (the cap authorizes this
    /// surface but not a write — an attenuated mirror). Drives the editor's
    /// read-only badge.
    pub fn is_read_only_under(&self, cap: &SurfaceCapability) -> bool {
        cap.surface() == self.surface && !is_write_rights(cap.rights())
    }

    /// Whether the backing cell is present + the buffer's authenticated digest
    /// in that cell MATCHES the visible document (i.e. the visible buffer is the
    /// committed one — no uncommitted edits). A buffer whose doc digest differs
    /// from the cell's stored digest has *unsaved* edits.
    pub fn is_clean(&self, world: &World) -> bool {
        match self.stored_digest(world) {
            Some(d) => d == self.doc.digest(),
            None => false,
        }
    }

    /// The digest the BACKING CELL currently stores (the last committed buffer
    /// content), or `None` if the cell is gone. The authenticated content bind.
    pub fn stored_digest(&self, world: &World) -> Option<FieldElement> {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| c.state.fields[BUFFER_DIGEST_SLOT])
    }

    /// The buffer's REVISION — the backing cell's nonce, advanced by each
    /// committed edit (the executor's receipt chain IS the buffer's edit
    /// history). `0` for a never-committed / missing buffer.
    pub fn revision(&self, world: &World) -> u64 {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    /// **COMMIT THE EDIT — the cap-gated, authenticated landing.** Writes the
    /// visible document's current digest into the backing cell (slot
    /// [`BUFFER_DIGEST_SLOT`]) through a REAL `Effect::SetField` turn on the
    /// embedded executor. Two gates fire, in order (mirroring
    /// [`crate::shell::Shell::present`]):
    ///   1. THE BUFFER-CAP GATE — `cap` must authorize a WRITE to this buffer
    ///      ([`Self::cap_can_write`]); a read-only mirror is REFUSED here
    ///      ([`BufferError::ReadOnly`]) BEFORE any turn runs (fail-closed).
    ///   2. THE EXECUTOR GATE — the `SetField` turn runs through the real
    ///      executor (its `Permissions` + whole-turn guarantees apply); a
    ///      rejection surfaces as [`BufferError::ExecutorRejected`].
    ///
    /// On success the backing cell's digest field = the new content AND its
    /// nonce advances (the revision), and a receipt is appended to the world's
    /// provenance. A refusal changes NOTHING. Returns the new revision.
    pub fn commit(&self, world: &mut World, cap: &SurfaceCapability) -> Result<u64, BufferError> {
        // (1) THE BUFFER-CAP GATE — anti cap-confusion + the read-only tooth.
        if cap.surface() != self.surface {
            return Err(BufferError::WrongSurface);
        }
        if !is_write_rights(cap.rights()) {
            return Err(BufferError::ReadOnly {
                held: rights_label(cap.rights()),
            });
        }
        // The backing cell must be live (a dangling buffer cannot commit).
        if world.ledger().get(&self.backing).is_none() {
            return Err(BufferError::Unbacked);
        }

        // (2) THE EXECUTOR GATE — write the new digest as a real verified turn.
        let digest = self.doc.digest();
        let turn = world.turn(
            self.backing,
            vec![world::set_field(self.backing, BUFFER_DIGEST_SLOT, digest)],
        );
        match world.commit_turn(turn) {
            crate::CommitOutcome::Committed { .. } => Ok(self.revision(world)),
            crate::CommitOutcome::Rejected { reason, .. } => {
                Err(BufferError::ExecutorRejected(reason))
            }
            // The world is suspended (meta-debug): the commit staged, did not land.
            crate::CommitOutcome::Queued { .. } => Err(BufferError::ExecutorRejected(
                "world suspended: turn queued, not committed".to_string(),
            )),
        }
    }
}

/// Whether a rights value is the FULL write authority. A buffer is writable iff
/// its cap holds the widest rights (`AuthRequired::None` — "no extra
/// authentication required", the original full grant the shell mints); any
/// attenuation (`Signature`/`Proof`/`Either`/`Impossible`/`Custom`) is a
/// read-only mirror. (Mirrors the A0 surface model where the opener holds the
/// full `None` cap and a SHARE narrows it.)
fn is_write_rights(r: &AuthRequired) -> bool {
    matches!(r, AuthRequired::None)
}

/// A short operator label for the rights a buffer cap holds.
fn rights_label(r: &AuthRequired) -> &'static str {
    match r {
        AuthRequired::None => "write",
        AuthRequired::Signature => "read-only(sig)",
        AuthRequired::Proof => "read-only(proof)",
        AuthRequired::Either => "read-only(either)",
        AuthRequired::Impossible => "locked",
        AuthRequired::Custom { .. } => "read-only(custom)",
    }
}

/// THE BUFFER VIEW — the gpui-free render model the cockpit maps onto its editor
/// pane. Built purely from a [`BufferCell`] + the live [`World`], so the panel
/// shows the AUTHENTICATED state of the buffer (its stored digest, revision,
/// dirty flag) alongside the visible text — never a self-report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BufferView {
    /// The buffer name (editor tab title).
    pub name: String,
    /// A short id for the backing cell (the authenticated anchor).
    pub backing_short: String,
    /// Whether the backing cell is present in the live ledger.
    pub backed: bool,
    /// Whether this buffer is READ-ONLY under the operator's held cap (an
    /// attenuated mirror — the editor shows the read-only badge + refuses edits).
    pub read_only: bool,
    /// Whether the visible buffer matches the last committed digest (no unsaved
    /// edits). `false` = the buffer has uncommitted changes (dirty).
    pub clean: bool,
    /// The buffer's revision (the backing cell's nonce — committed-edit count).
    pub revision: u64,
    /// A short hex of the VISIBLE document's digest (the would-be next commit).
    pub doc_digest_short: String,
    /// A short hex of the STORED (committed) digest, if any.
    pub stored_digest_short: Option<String>,
    /// The buffer's lines (the editor body).
    pub lines: Vec<String>,
    /// The cursor's byte offset (for the status line).
    pub cursor: usize,
}

impl BufferView {
    /// Build the view from a buffer + the live world, given the operator's held
    /// cap (which decides the read-only badge). `cap` is `None` when the
    /// operator holds no cap for this buffer at all (then it is shown read-only —
    /// no authority means no edits).
    pub fn build(buf: &BufferCell, world: &World, cap: Option<&SurfaceCapability>) -> Self {
        let backed = world.ledger().get(&buf.backing).is_some();
        let read_only = match cap {
            Some(c) => !buf.cap_can_write(c),
            None => true,
        };
        let stored = buf.stored_digest(world);
        BufferView {
            name: buf.name.clone(),
            backing_short: crate::reflect::short_hex(buf.backing.as_bytes()),
            backed,
            read_only,
            clean: buf.is_clean(world),
            revision: buf.revision(world),
            doc_digest_short: buf.doc.digest_short(),
            stored_digest_short: stored.map(|d| crate::reflect::short_hex(&d)),
            lines: buf.doc.lines().map(|l| l.to_string()).collect(),
            cursor: buf.doc.cursor(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shell::Shell;

    /// A shell + world + a writable buffer over a fresh cell, plus the writable
    /// cap the shell minted. The buffer renders into the surface the shell opened.
    fn writable_buffer() -> (Shell, World, BufferCell, SurfaceCapability) {
        let mut world = World::new();
        let backing = world.genesis_cell(0x5B, 0);
        let mut shell = Shell::new();
        // Open the buffer's window through the A0 shell — it mints the FULL
        // (writable) surface cap (the opener holds `AuthRequired::None`).
        let cap = shell.open_cell_view(backing, "buffer.txt");
        let buf = BufferCell::new(cap.surface(), backing, "buffer.txt", "hello\nworld");
        (shell, world, buf, cap)
    }

    #[test]
    fn the_doc_digest_binds_the_text() {
        // The content digest is a function of the text — a different buffer gives
        // a different digest (the §5 bind for a buffer; the pale ghost can't
        // claim content it doesn't hold).
        let a = BufferDoc::from_text("hello");
        let b = BufferDoc::from_text("world");
        assert_ne!(a.digest(), b.digest(), "different text ⇒ different digest");
        assert_eq!(
            a.digest(),
            BufferDoc::from_text("hello").digest(),
            "the digest is a function"
        );
    }

    #[test]
    fn editing_the_doc_is_free_and_does_not_touch_the_ledger() {
        // Typing into the VIEW is free — it mutates the in-memory doc only; the
        // ledger is untouched until a cap-gated commit.
        let (_shell, world, mut buf, _cap) = writable_buffer();
        let h0 = world.height();
        buf.doc_mut().insert("!");
        assert_eq!(
            world.height(),
            h0,
            "in-memory edits do not advance the ledger"
        );
        assert!(buf.doc().text().ends_with('!'));
    }

    #[test]
    fn backspace_handles_boundaries() {
        let mut d = BufferDoc::from_text("ab");
        d.backspace();
        assert_eq!(d.text(), "a");
        d.backspace();
        assert_eq!(d.text(), "");
        d.backspace(); // no-op at the start
        assert_eq!(d.text(), "");
    }

    // ── THE COMMIT POLARITY: a writable buffer's edit lands as a verified turn ──

    #[test]
    fn a_writable_buffer_commits_an_edit_as_a_real_turn() {
        // THE GROUNDED SEAM: committing an edit writes the new digest into the
        // backing cell through the REAL executor, advancing the revision +
        // appending a receipt (the buffer's authority/provenance is real).
        let (_shell, mut world, buf, cap) = writable_buffer();
        assert!(buf.cap_can_write(&cap), "the opener holds the write cap");

        // Initially dirty: the cell stores the zero digest, the doc has text.
        assert!(
            !buf.is_clean(&world),
            "a fresh buffer with text is dirty (uncommitted)"
        );

        let h0 = world.height();
        let rev = buf
            .commit(&mut world, &cap)
            .expect("a writable edit commits");
        assert!(rev >= 1, "the revision advanced (the backing cell's nonce)");
        assert_eq!(world.height(), h0 + 1, "a real turn was committed");
        assert_eq!(
            world.receipts().len(),
            1,
            "a receipt was appended (provenance)"
        );
        // The backing cell now stores the buffer's content digest (the bind).
        assert_eq!(buf.stored_digest(&world), Some(buf.doc().digest()));
        assert!(
            buf.is_clean(&world),
            "after commit the buffer is clean (no unsaved edits)"
        );
    }

    #[test]
    fn a_second_edit_advances_the_revision_again() {
        let (_shell, mut world, mut buf, cap) = writable_buffer();
        buf.commit(&mut world, &cap).unwrap();
        let rev1 = buf.revision(&world);
        // Edit the doc + commit again → the revision advances (the receipt chain
        // IS the buffer's edit history).
        buf.doc_mut().insert("\nmore");
        let rev2 = buf
            .commit(&mut world, &cap)
            .expect("the second edit commits");
        assert!(rev2 > rev1, "each committed edit advances the revision");
        assert_eq!(world.receipts().len(), 2, "two edits → two receipts");
    }

    // ── THE READ-ONLY POLARITY: a write to a read-only buffer REFUSES ──

    #[test]
    fn a_write_to_a_read_only_buffer_is_refused() {
        // THE READ-ONLY TOOTH: a read-only buffer holds an ATTENUATED cap
        // (a Signature mirror, narrowed from the writable None). A commit through
        // it is REFUSED by the buffer-cap gate BEFORE any turn runs (fail-closed,
        // no-amplification at the editor) — and the ledger is untouched.
        let mut world = World::new();
        let backing = world.genesis_cell(0x5C, 0);
        let mut shell = Shell::new();
        let writable = shell.open_cell_view(backing, "ro.txt");
        // SHARE a READ-ONLY mirror through the A0 shell (a real GrantCapability
        // turn narrows None → Signature). This is the read-only buffer's cap.
        let ro_cap = shell
            .share(
                &writable,
                /*recipient app*/ 0x4E0,
                AuthRequired::Signature,
            )
            .expect("a narrowing (read-only) share commits");
        assert_eq!(ro_cap.rights(), &AuthRequired::Signature);

        // The read-only buffer renders into the shared surface.
        let buf = BufferCell::new(ro_cap.surface(), backing, "ro.txt", "frozen text");
        assert!(buf.is_read_only_under(&ro_cap), "the mirror is read-only");
        assert!(
            !buf.cap_can_write(&ro_cap),
            "a read-only mirror cannot write"
        );

        let h0 = world.height();
        let r = buf.commit(&mut world, &ro_cap);
        assert!(
            matches!(r, Err(BufferError::ReadOnly { .. })),
            "a write to a read-only buffer must be REFUSED, got {r:?}"
        );
        // Fail-closed: nothing changed (no turn, no receipt).
        assert_eq!(world.height(), h0, "a refused edit commits no turn");
        assert_eq!(
            world.receipts().len(),
            0,
            "a refused edit appends no receipt"
        );
    }

    #[test]
    fn a_cap_for_another_buffer_is_refused_cap_confusion() {
        // A cap that authorizes a DIFFERENT surface cannot drive this buffer
        // (anti cap-confusion) — refused before any turn.
        let (_shell, mut world, buf, _cap) = writable_buffer();
        // A cap naming a different surface id (even with write rights) is wrong.
        let foreign = SurfaceCapability::new(
            crate::surface::SurfaceId(buf.surface().as_u64().wrapping_add(99)),
            dregg_firmament::Capability::surface(buf.backing(), AuthRequired::None),
        );
        let r = buf.commit(&mut world, &foreign);
        assert!(
            matches!(r, Err(BufferError::WrongSurface)),
            "cap confusion refused, got {r:?}"
        );
    }

    // ── THE VIEW: the panel model reflects the AUTHENTICATED buffer state ──

    #[test]
    fn the_view_reflects_dirty_then_clean_and_the_read_only_badge() {
        let (_shell, mut world, buf, cap) = writable_buffer();
        // A writable buffer with uncommitted text: not read-only, dirty.
        let v0 = BufferView::build(&buf, &world, Some(&cap));
        assert!(
            !v0.read_only,
            "the writable buffer is not read-only under its write cap"
        );
        assert!(!v0.clean, "it has uncommitted edits (dirty)");
        assert_eq!(v0.lines, vec!["hello".to_string(), "world".to_string()]);
        assert!(v0.stored_digest_short.is_some(), "the backing cell is live");

        // Commit → clean, revision advanced.
        buf.commit(&mut world, &cap).unwrap();
        let v1 = BufferView::build(&buf, &world, Some(&cap));
        assert!(v1.clean, "after commit the view is clean");
        assert_eq!(v1.revision, buf.revision(&world));

        // With NO held cap, the view is read-only (no authority ⇒ no edits).
        let v2 = BufferView::build(&buf, &world, None);
        assert!(v2.read_only, "no held cap ⇒ read-only");
    }

    #[test]
    fn a_buffer_over_a_missing_cell_is_unbacked_and_cannot_commit() {
        // A buffer whose backing cell is not in the ledger is shown unbacked and
        // its commit refuses (a dangling buffer can't land an edit).
        let mut world = World::new();
        let ghost = CellId::from_bytes([0x99; 32]); // never installed
        let mut shell = Shell::new();
        let cap = shell.open_cell_view(ghost, "ghost.txt");
        let buf = BufferCell::new(cap.surface(), ghost, "ghost.txt", "void");
        let v = BufferView::build(&buf, &world, Some(&cap));
        assert!(!v.backed, "a missing cell is unbacked");
        let r = buf.commit(&mut world, &cap);
        assert!(
            matches!(r, Err(BufferError::Unbacked)),
            "a dangling buffer cannot commit, got {r:?}"
        );
    }
}
