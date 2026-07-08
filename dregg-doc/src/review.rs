//! REVIEW THREADS — comments + approvals as cryptographically-OWNED, receipted
//! document atoms (docs/deos/DREGG-FORGE.md, the review half of the forge).
//!
//! A code review today (in the [`crate::pull_request`] slice) is only its
//! *resolution* patch set — the settlements that make the merge clean. This
//! module adds the other half: real review THREADS. A comment is not a database
//! row someone can set; it is a **document atom** authored by its reviewer,
//! appended to the review thread as a cap-gated, finalized, journaled turn
//! through the REAL executor ([`ExecutorDrivenDoc::edit`]). Everything the patch
//! core already guarantees rides for free:
//!
//! - **Owned, not settable.** A comment lands only by driving an [`Op::Add`]
//!   patch [`Patch::by`]`(reviewer, ..)` through [`ExecutorDrivenDoc::edit`] —
//!   the crate's sole `TurnExecutor::execute` entry, where
//!   `check_cross_cell_permission` gates the write. A reviewer whose editor
//!   lacks the thread region's **review cap** is refused IN-BAND
//!   ([`dregg_turn::TurnError::CapabilityNotHeld`]) and the thread is
//!   byte-untouched — the only way in is a receipted turn the executor signs
//!   off on.
//! - **Attributable by blame — bound to the authenticated editor.** Each
//!   comment atom carries its reviewer as [`crate::Provenance`]; the reviewer is
//!   NOT a caller-chosen label but [`author_of_editor`]`(doc.editor_id())`, a
//!   deterministic projection of the editor cell whose cap gated the write
//!   ([`ReviewThread::comment`] refuses any other claimed author with
//!   [`dregg_turn::TurnError::InvalidAuthorization`] before driving the turn).
//!   So there is genuinely NO forge-an-author path: a single cap-holder cannot
//!   blame a post to an arbitrary reviewer — blame IS the authenticated editor.
//!   [`crate::blame`] reads "who said what" straight off the committed atom —
//!   stable across every later post (the git-blame middle-insert smear cannot
//!   happen).
//! - **Immutable once said.** A posted comment is a committed atom bound in the
//!   region cell's `fields_root`; this API offers no edit/delete of it, and a
//!   forged author would move the commitment (§4.4 anti-forge).
//! - **Ordered.** Each post is `Add`-ed after the thread's current tip, so the
//!   thread is a linear chain and [`crate::blame`]'s document-order walk reads
//!   comments back in the order they were posted; a second reviewer's comment
//!   coexists (a multi-author thread).
//!
//! An **approval** is the same receipted-turn path with a distinguished marker
//! atom (the [`APPROVAL_TAG`] content) authored by the approver — so an approval
//! is as owned, attributable, and immutable as any comment.
//!
//! ## The kind lives in the committed content (not a side-flag)
//!
//! A review atom's KIND (comment vs approval) is a committed content tag
//! ([`COMMENT_TAG`] / [`APPROVAL_TAG`]) bound inside the atom's leaf, so a light
//! client reads it off the same root it trusts. It is not a mutable field
//! someone can flip after the fact — the same non-forgeability the author gets.
//!
//! ## Approval-as-required-check (welded to CI-as-receipted-turns)
//!
//! An approval post yields a committed, executor-signed [`dregg_turn::TurnReceipt`]
//! — exactly the witness kind [`crate::check::RequiredCheck::committed_receipt`]
//! already verifies. So "merge requires N approvals" reuses the CI gate with NO
//! new machinery: [`ReviewThread::planned_approval_check`] binds a
//! [`crate::check::RequiredCheck`] to the exact approval turn (nameable before it
//! runs, [`ExecutorDrivenDoc::planned_turn_hash`]), and the approval receipt is
//! the committed witness that satisfies it at land time.
//!
//! ## Named seams (deferred, not holes)
//!
//! - **Per-line / inline threads**: here the thread is a flat conversation
//!   ordered by post time. Anchoring a comment to a specific code atom /
//!   conflict-region / path (an inline review comment) is a natural next slice —
//!   a comment atom would carry the anchored atom id and the surface would group
//!   threads by anchor. The owned-turn + blame machinery is unchanged; only the
//!   grouping key is added.
//! - **The deos-view review surface**: rendering threads (comments + approval
//!   state) in the cockpit's PR view is a `deos-view` job, not built here.
//! - **Per-reviewer editor cells over one thread region**: in-process an
//!   [`ExecutorDrivenDoc`] bundles one editor cell with one region cell, so a
//!   multi-author thread posts distinct [`Author`]s through one cap-holding doc.
//!   Distinct reviewers each holding their OWN cap to the SAME thread region
//!   (so the cap gate discriminates per reviewer) is the federated forge-grain
//!   shape — the same seam [`crate::pull_request`] names.

use crate::atom::{AtomId, Author, PatchId};
use crate::blame::blame;
use crate::graph::DocGraph;

#[cfg(feature = "substrate")]
use crate::executor_drive::ExecutorDrivenDoc;
#[cfg(feature = "substrate")]
use crate::patch::Patch;
#[cfg(feature = "substrate")]
use dregg_cell::CellId;
#[cfg(feature = "substrate")]
use dregg_turn::{TurnError, TurnReceipt};

/// Derive the provenance [`Author`] BOUND to an executor-authenticated editor
/// cell — the non-forgeable identity a review post's blame carries.
///
/// A review post's [`Author`] is NOT a caller-chosen label; it is a
/// deterministic projection of the editor cell that the executor authenticated
/// as the turn's agent ([`ExecutorDrivenDoc::editor_id`]). [`ReviewThread::comment`]
/// / [`ReviewThread::approve`] stamp exactly this author, so "who said what" is
/// bound to the cell whose capability gated the write — there is no path to
/// blame a post to a cell you did not authenticate as.
///
/// Because [`Author`] is a 64-bit tag (`atom::Author(u64)`) while a [`CellId`]
/// is 256 bits, this is a FOLD, not an injection: it maps each editor cell to a
/// stable `Author` via a splitmix64-style avalanche of the cell-id bytes. Two
/// DISTINCT editor cells folding to the same `Author` is a ~2⁻⁶⁴ accident and,
/// even then, only MERGES their blame — it never lets a non-editor forge an
/// author (you still cannot drive the turn without the editor cell's cap). The
/// full 256-bit editor identity remains the [`CellId`] the receipt's `agent`
/// carries; this fold is the document-blame VIEW of that identity.
#[cfg(feature = "substrate")]
pub fn author_of_editor(editor: CellId) -> Author {
    let mut acc: u64 = 0x9E37_79B9_7F4A_7C15;
    for chunk in editor.as_bytes().chunks_exact(8) {
        let w = u64::from_le_bytes(chunk.try_into().unwrap());
        acc ^= w;
        acc = acc.wrapping_mul(0xBF58_476D_1CE4_E5B9);
        acc ^= acc >> 31;
    }
    Author(acc)
}

/// The committed content tag marking a review atom as a COMMENT; the reviewer's
/// prose follows the tag. Bound inside the atom's committed leaf, so the atom's
/// KIND is part of the commitment a light client trusts — not a mutable flag.
pub const COMMENT_TAG: &str = "\u{1}dregg-review/comment\u{1}";
/// The committed content tag marking a review atom as an APPROVAL (a
/// distinguished marker atom authored by the approver).
pub const APPROVAL_TAG: &str = "\u{1}dregg-review/approve\u{1}";

/// A comment read back off the committed thread graph: the atom it lives in, its
/// reviewer (from provenance — a *fact*), the patch that posted it, and the
/// reviewer's prose (the tag stripped).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ReviewComment {
    /// The content-addressed atom holding this comment (stable across later posts).
    pub atom: AtomId,
    /// Who wrote it (read off the atom's provenance — attributable by blame).
    pub author: Author,
    /// The patch that introduced this comment atom.
    pub patch: PatchId,
    /// The reviewer's prose (the [`COMMENT_TAG`] stripped).
    pub text: String,
}

/// An approval read back off the committed thread graph: the marker atom, its
/// approver, and the patch that posted it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Approval {
    /// The content-addressed approval marker atom.
    pub atom: AtomId,
    /// Who approved (read off the atom's provenance).
    pub author: Author,
    /// The patch that introduced this approval atom.
    pub patch: PatchId,
}

/// Read every COMMENT off a committed thread graph, in post order.
///
/// Walks the live atoms in document order ([`crate::blame`]) — a comment is
/// never deleted, so the thread is a linear chain and the read order IS the post
/// order. Attribution comes straight off each atom's provenance.
pub fn comments_of(g: &DocGraph) -> Vec<ReviewComment> {
    blame(g)
        .into_iter()
        .filter_map(|b| {
            b.content
                .strip_prefix(COMMENT_TAG)
                .map(|text| ReviewComment {
                    atom: b.atom,
                    author: b.author,
                    patch: b.patch,
                    text: text.to_string(),
                })
        })
        .collect()
}

/// Read every APPROVAL off a committed thread graph, in post order (attributed
/// off each marker atom's provenance).
pub fn approvals_of(g: &DocGraph) -> Vec<Approval> {
    blame(g)
        .into_iter()
        .filter_map(|b| {
            b.content.strip_prefix(APPROVAL_TAG).map(|_| Approval {
                atom: b.atom,
                author: b.author,
                patch: b.patch,
            })
        })
        .collect()
}

/// A REVIEW THREAD carried on a [`crate::PullRequest`]: the post-order tip + the
/// receipted-turn evidence of every post. The thread's CONTENT is committed in a
/// backing [`ExecutorDrivenDoc`] (a region cell distinct from the PR's code
/// document — commenting caps are independent of the land/edit cap, exactly as a
/// reviewer can comment without being able to merge); this object holds the
/// linearization tip and the receipt chain the posts left.
#[cfg(feature = "substrate")]
#[derive(Clone, Debug)]
pub struct ReviewThread {
    /// The tip of the comment chain — the atom each new post is `Add`-ed after
    /// ([`AtomId::ROOT`] before the first post). Preserves post order.
    tip: AtomId,
    /// A monotone per-post seed: distinct posts (even identical prose by the
    /// same reviewer) get distinct atom ids — each comment is its own event.
    seq: u64,
    /// The finalized, journaled executor receipt of every landed post, in order
    /// — the owned-turn evidence (a post that never landed left none).
    receipts: Vec<TurnReceipt>,
}

#[cfg(feature = "substrate")]
impl Default for ReviewThread {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "substrate")]
impl ReviewThread {
    /// A fresh, empty thread (its first post is `Add`-ed after [`AtomId::ROOT`]).
    pub fn new() -> Self {
        ReviewThread {
            tip: AtomId::ROOT,
            seq: 0,
            receipts: Vec::new(),
        }
    }

    /// The exact `(new atom id, authored patch)` the next [`ReviewThread::comment`]
    /// will drive — an [`Op::Add`] of the tagged comment after the current tip.
    fn next_comment(&self, author: Author, text: &str) -> (AtomId, Patch) {
        let content = format!("{COMMENT_TAG}{text}");
        let (id, op) = Patch::add(self.seq, &content, self.tip);
        (id, Patch::by(author, [op]))
    }

    /// The exact `(new atom id, authored patch)` the next [`ReviewThread::approve`]
    /// will drive — an [`Op::Add`] of the approval marker after the current tip.
    fn next_approval(&self, author: Author) -> (AtomId, Patch) {
        let (id, op) = Patch::add(self.seq, APPROVAL_TAG, self.tip);
        (id, Patch::by(author, [op]))
    }

    /// The exact patch the next [`ReviewThread::approve`] post on `doc` will
    /// drive. Exposed so a caller can plan its turn hash
    /// ([`ExecutorDrivenDoc::planned_turn_hash`]) — the binding surface for
    /// approval-as-required-check ([`ReviewThread::planned_approval_check`]).
    /// The approval's author is bound to `doc`'s authenticated editor cell
    /// ([`author_of_editor`]), exactly as the [`ReviewThread::approve`] post
    /// that satisfies the plan — so the planned turn hash matches the post.
    pub fn approval_patch(&self, doc: &ExecutorDrivenDoc) -> Patch {
        self.next_approval(author_of_editor(doc.editor_id())).1
    }

    /// POST A COMMENT — a receipted, cap-gated, finalized turn appending the
    /// reviewer's prose to the thread.
    ///
    /// The comment is an [`Op::Add`] patch [`Patch::by`]`(author, ..)` driven
    /// through [`ExecutorDrivenDoc::edit`] on the thread's backing region cell.
    /// A reviewer whose editor holds the region's review cap lands the atom
    /// (finalized, journaled); one WITHOUT it is refused IN-BAND
    /// ([`TurnError::CapabilityNotHeld`]) and NOTHING lands — the thread is
    /// byte-untouched (the executor rolled back) and this object's tip/seq are
    /// not advanced.
    ///
    /// **Blame is bound to the authenticated editor.** `author` MUST equal
    /// [`author_of_editor`]`(doc.editor_id())` — the identity of the cell whose
    /// cap gates this write. A post claiming any OTHER author is refused with
    /// [`TurnError::InvalidAuthorization`] BEFORE any turn is driven (the thread
    /// untouched), so a single cap-holder cannot stamp blame to an arbitrary
    /// author. Multi-author threads therefore need multiple editor cells (the
    /// named per-reviewer-caps seam), one per reviewer identity.
    pub fn comment(
        &mut self,
        doc: &mut ExecutorDrivenDoc,
        author: Author,
        text: &str,
    ) -> Result<TurnReceipt, TurnError> {
        let bound = Self::require_bound_author(doc, author)?;
        let (id, patch) = self.next_comment(bound, text);
        let receipt = doc.edit(patch)?;
        self.advance(id, receipt.clone());
        Ok(receipt)
    }

    /// POST AN APPROVAL — the same receipted-turn path with a distinguished
    /// marker atom ([`APPROVAL_TAG`]) authored by the authenticated editor.
    /// Refused in-band for a non-cap-holder, exactly like
    /// [`ReviewThread::comment`]; and `author` must be bound to `doc`'s editor
    /// cell (see [`ReviewThread::comment`]) or the post is refused with
    /// [`TurnError::InvalidAuthorization`].
    pub fn approve(
        &mut self,
        doc: &mut ExecutorDrivenDoc,
        author: Author,
    ) -> Result<TurnReceipt, TurnError> {
        let bound = Self::require_bound_author(doc, author)?;
        let (id, patch) = self.next_approval(bound);
        let receipt = doc.edit(patch)?;
        self.advance(id, receipt.clone());
        Ok(receipt)
    }

    /// The blame-binding gate: the claimed `author` must be the identity of
    /// `doc`'s executor-authenticated editor cell ([`author_of_editor`]).
    /// Returns that bound author on success, or refuses a forged one with
    /// [`TurnError::InvalidAuthorization`] — the non-forgeable-blame invariant.
    fn require_bound_author(doc: &ExecutorDrivenDoc, author: Author) -> Result<Author, TurnError> {
        let bound = author_of_editor(doc.editor_id());
        if author != bound {
            return Err(TurnError::InvalidAuthorization {
                reason:
                    "review post's author is not the authenticated editor cell — blame is bound to the editor identity (author_of_editor)"
                        .to_string(),
            });
        }
        Ok(bound)
    }

    /// Advance the thread ONLY after a post committed (a refused post never
    /// reaches here — the thread stays exactly as it was).
    fn advance(&mut self, new_tip: AtomId, receipt: TurnReceipt) {
        self.tip = new_tip;
        self.seq += 1;
        self.receipts.push(receipt);
    }

    /// The finalized receipts of every landed post (the owned-turn evidence).
    pub fn receipts(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    /// Read every comment off the thread's backing document, in post order,
    /// attributed by blame.
    pub fn comments(&self, doc: &ExecutorDrivenDoc) -> Vec<ReviewComment> {
        comments_of(doc.graph())
    }

    /// Read every approval off the thread's backing document, attributed by
    /// blame (immutable — this API offers no path to alter a posted approval).
    pub fn approvals(&self, doc: &ExecutorDrivenDoc) -> Vec<Approval> {
        approvals_of(doc.graph())
    }

    /// How many approvals the thread carries.
    pub fn approval_count(&self, doc: &ExecutorDrivenDoc) -> usize {
        approvals_of(doc.graph()).len()
    }

    /// APPROVAL-AS-REQUIRED-CHECK: the [`crate::check::RequiredCheck`] a merge
    /// that "requires an approval" carries, bound to the EXACT turn the next
    /// [`ReviewThread::approve`] post on `doc` will commit and trusting `keys`
    /// (the thread executor's verifying key). The approving identity is `doc`'s
    /// authenticated editor cell ([`author_of_editor`]) — the same non-forgeable
    /// author the `approve` post stamps — so the planned turn hash matches the
    /// post. The approval receipt returned by `approve` is then the committed,
    /// signed witness that satisfies it — verified by [`crate::check`] as any
    /// other committed-receipt check, no new machinery. `None` if the approval
    /// turn has no projection delta (never, for a fresh approval atom).
    ///
    /// The plan matches the post iff no edit interleaves on `doc` between this
    /// call and the `approve` (turn construction is deterministic — see
    /// [`ExecutorDrivenDoc::planned_turn_hash`]).
    pub fn planned_approval_check(
        &self,
        doc: &ExecutorDrivenDoc,
        id: impl Into<crate::check::CheckId>,
        trusted_executor_keys: Vec<[u8; 32]>,
    ) -> Option<crate::check::RequiredCheck> {
        let patch = self.approval_patch(doc);
        let hash = doc.planned_turn_hash(&patch)?;
        Some(crate::check::RequiredCheck::committed_receipt(
            id,
            hash,
            trusted_executor_keys,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::patch::Patch;

    // ── the reading side, on a plain graph (no substrate) ───────────────────

    #[test]
    fn comments_and_approvals_read_off_a_plain_graph_attributed_and_ordered() {
        // Hand-build a thread graph: a comment by Author(3), then an approval by
        // Author(5), chained — the shape a posted thread commits to.
        let mut g = DocGraph::new();
        let (c1, op1) = Patch::add(1, &format!("{COMMENT_TAG}looks good"), AtomId::ROOT);
        Patch::by(Author(3), [op1]).apply(&mut g);
        let (_a1, op2) = Patch::add(2, APPROVAL_TAG, c1);
        Patch::by(Author(5), [op2]).apply(&mut g);

        let comments = comments_of(&g);
        assert_eq!(comments.len(), 1, "one comment");
        assert_eq!(comments[0].author, Author(3), "attributed to its reviewer");
        assert_eq!(comments[0].text, "looks good", "the tag is stripped");

        let approvals = approvals_of(&g);
        assert_eq!(approvals.len(), 1, "one approval");
        assert_eq!(approvals[0].author, Author(5), "attributed to its approver");

        // The comment atom is not misread as an approval, nor vice versa.
        assert_ne!(comments[0].atom, approvals[0].atom);
    }

    // ── the receipted-turn poles (substrate) ────────────────────────────────

    #[cfg(feature = "substrate")]
    mod thread {
        use super::*;
        use crate::content::content;
        use dregg_turn::{Finality, TurnError};

        /// RFC 8032 §7.1 TEST 1 Ed25519 (seed, verifying-key) pair — the same
        /// real pair the pull_request CI-gate tests use; the executor derives
        /// this pubkey from this seed by standard key generation.
        const SIGNING_SEED: [u8; 32] = [
            0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec,
            0x2c, 0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03,
            0x1c, 0xae, 0x7f, 0x60,
        ];
        const VERIFYING_KEY: [u8; 32] = [
            0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64,
            0x07, 0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68,
            0xf7, 0x07, 0x51, 0x1a,
        ];

        #[test]
        fn a_cap_holding_reviewers_comment_lands_as_a_receipted_turn_attributable_via_blame() {
            // The reviewer's editor HOLDS the thread region's review cap.
            let mut thread = ReviewThread::new();
            let mut doc = ExecutorDrivenDoc::new(1, 2, /* holds review cap */ true);
            let pre = doc.state_commitment();

            // Blame is BOUND to the authenticated editor: the reviewer's author
            // is derived from the editor cell, not a free label.
            let reviewer = author_of_editor(doc.editor_id());
            let receipt = thread
                .comment(&mut doc, reviewer, "needs a test")
                .expect("a cap-holding reviewer's comment lands");

            // A REAL finalized, journaled executor turn — not a settable field.
            assert_eq!(
                receipt.finality,
                Finality::Final,
                "the comment landed as a finalized executor commit"
            );
            assert_eq!(
                receipt.agent,
                doc.editor_id(),
                "the reviewer drove the turn"
            );
            assert_ne!(
                doc.state_commitment(),
                pre,
                "the comment moved the commitment"
            );
            assert!(doc.commitment_matches_projection());
            assert_eq!(thread.receipts().len(), 1, "the owned-turn evidence");

            // Attributable by blame, reads back in the thread — bound to the
            // authenticated editor cell.
            let comments = thread.comments(&doc);
            assert_eq!(comments.len(), 1);
            assert_eq!(
                comments[0].author, reviewer,
                "blame attributes the authenticated editor"
            );
            assert_eq!(
                comments[0].author,
                author_of_editor(doc.editor_id()),
                "the blamed author IS the editor identity"
            );
            assert_eq!(comments[0].text, "needs a test");
        }

        /// FIX #4a: a cap-holder CANNOT stamp blame to an arbitrary author — a
        /// post claiming any identity other than the authenticated editor cell
        /// is refused with `InvalidAuthorization` BEFORE any turn is driven, and
        /// the thread is byte-untouched. Blame is non-forgeable.
        #[test]
        fn a_forged_author_is_refused_and_the_thread_is_untouched() {
            let mut thread = ReviewThread::new();
            let mut doc = ExecutorDrivenDoc::new(1, 2, /* holds review cap */ true);
            let pre = doc.state_commitment();

            let editor = author_of_editor(doc.editor_id());
            // Claim SOMEONE ELSE's author (guaranteed distinct from the editor's).
            let forged = Author(editor.0 ^ 0xDEAD_BEEF);
            assert_ne!(forged, editor);

            match thread.comment(&mut doc, forged, "blame you") {
                Err(TurnError::InvalidAuthorization { .. }) => {}
                other => panic!("expected InvalidAuthorization for a forged author, got {other:?}"),
            }
            // Nothing landed: the forge never reached the executor.
            assert_eq!(doc.state_commitment(), pre, "the forged post did not land");
            assert!(
                thread.comments(&doc).is_empty(),
                "no forged comment in the thread"
            );
            assert!(thread.receipts().is_empty(), "no owned-turn evidence");

            // The SAME post, correctly claiming the editor identity, lands.
            thread
                .comment(&mut doc, editor, "blame you")
                .expect("the authenticated editor's own post lands");
            let comments = thread.comments(&doc);
            assert_eq!(comments.len(), 1);
            assert_eq!(comments[0].author, editor, "blamed to the real editor");

            // An approval forge is refused on the same gate.
            let mut thread2 = ReviewThread::new();
            let mut doc2 = ExecutorDrivenDoc::new(3, 4, true);
            match thread2.approve(&mut doc2, Author(author_of_editor(doc2.editor_id()).0 ^ 1)) {
                Err(TurnError::InvalidAuthorization { .. }) => {}
                other => {
                    panic!("expected InvalidAuthorization for a forged approver, got {other:?}")
                }
            }
            assert!(thread2.approvals(&doc2).is_empty());
        }

        /// Two posts on ONE editor cell coexist and preserve post order; both
        /// blame to the SAME authenticated editor identity (blame binding — a
        /// genuinely multi-author thread requires multiple editor cells, the
        /// named per-reviewer-caps seam).
        #[test]
        fn a_second_comment_coexists_order_preserved_same_editor_identity() {
            let mut thread = ReviewThread::new();
            let mut doc = ExecutorDrivenDoc::new(1, 2, true);
            let editor = author_of_editor(doc.editor_id());

            thread
                .comment(&mut doc, editor, "first")
                .expect("first comment");
            thread
                .comment(&mut doc, editor, "second")
                .expect("second comment");

            let comments = thread.comments(&doc);
            assert_eq!(comments.len(), 2, "both comments coexist");
            // ORDER preserved (post order = document order via blame).
            assert_eq!(comments[0].author, editor);
            assert_eq!(comments[0].text, "first");
            assert_eq!(comments[1].author, editor);
            assert_eq!(comments[1].text, "second");
            // Both posts blame to the SAME authenticated editor (binding): a
            // multi-author thread needs multiple editor cells.
            assert_eq!(comments[0].author, comments[1].author);
            assert_eq!(thread.receipts().len(), 2);
            // The receipt chain links the second post off the first.
            assert_eq!(
                thread.receipts()[1].previous_receipt_hash,
                Some(thread.receipts()[0].receipt_hash()),
                "the posts are receipt-chained"
            );
        }

        #[test]
        fn a_non_holder_comment_is_refused_in_band_thread_untouched() {
            // The reviewer's editor LACKS the thread region's review cap. The
            // reviewer honestly claims its own (editor-bound) identity — so the
            // refusal here is the CAP gate, not the author-binding gate.
            let mut thread = ReviewThread::new();
            let mut doc = ExecutorDrivenDoc::new(1, 2, /* holds review cap */ false);
            let pre = doc.state_commitment();
            let reviewer = author_of_editor(doc.editor_id());

            match thread.comment(&mut doc, reviewer, "sneak") {
                Err(TurnError::CapabilityNotHeld { actor, target }) => {
                    assert_eq!(actor, doc.editor_id(), "the reviewer is the refused actor");
                    assert_eq!(target, doc.region_id(), "the thread region is gated");
                }
                other => panic!("expected an in-band CapabilityNotHeld refusal, got {other:?}"),
            }

            // The thread is BYTE-UNTOUCHED: no comment landed.
            assert_eq!(doc.state_commitment(), pre, "nothing landed");
            assert!(thread.comments(&doc).is_empty(), "no comment in the thread");
            assert!(thread.receipts().is_empty(), "no owned-turn evidence");
            assert_eq!(content(doc.graph()).to_marked_string(), "", "thread empty");

            // WITH the cap, the same post is admitted (its own editor identity).
            let mut held = ExecutorDrivenDoc::new(1, 2, true);
            thread
                .comment(&mut held, author_of_editor(held.editor_id()), "sneak")
                .expect("a cap-holding reviewer is admitted");
            assert_eq!(thread.comments(&held).len(), 1);
        }

        #[test]
        fn approvals_read_back_attributable_and_immutable() {
            let mut thread = ReviewThread::new();
            let mut doc = ExecutorDrivenDoc::new(1, 2, true);
            let approver = author_of_editor(doc.editor_id());

            thread.approve(&mut doc, approver).expect("first approval");
            thread.approve(&mut doc, approver).expect("second approval");

            let approvals = thread.approvals(&doc);
            assert_eq!(approvals.len(), 2, "both approvals read back");
            // Attributable — bound to the authenticated editor cell.
            assert_eq!(approvals[0].author, approver, "attributable to the editor");
            assert_eq!(approvals[1].author, approver, "attributable to the editor");
            assert_eq!(thread.approval_count(&doc), 2);

            // IMMUTABLE: reading does not mutate; the committed state is stable
            // and there is no API to alter a posted approval.
            let committed = doc.state_commitment();
            let reread = thread.approvals(&doc);
            assert_eq!(reread, approvals, "the approval set is stable");
            assert_eq!(doc.state_commitment(), committed, "reading is pure");

            // Approvals do not masquerade as comments.
            assert!(thread.comments(&doc).is_empty());
        }

        #[test]
        fn an_approval_satisfies_a_required_check_and_gates_the_merge() {
            use crate::check::{CheckRefusal, CheckWitness};
            use crate::history::History;
            use crate::patch::Op;
            use crate::pull_request::{PullRequest, PullRequestError};

            // A clean PR: base tombstones "one", head appends "three" — disjoint.
            let clean_pr = || {
                let mut h = History::new();
                let (s1, op1) = Patch::add(1, "one\n", AtomId::ROOT);
                let (s2, op2) = Patch::add(2, "two\n", s1);
                h.commit(Patch::by(Author(0), [op1]));
                h.commit(Patch::by(Author(0), [op2]));
                let mut base = h.branch();
                base.commit(Patch::by(Author(1), [Op::Delete { id: s1 }]));
                let mut head = h.branch();
                head.commit(Patch::by(Author(2), [Patch::add(3, "three\n", s2).1]));
                PullRequest::open(base, head)
            };

            // The thread's backing executor SIGNS its receipts (the
            // non-fabricable part of the committed-receipt witness).
            let mut thread_doc = ExecutorDrivenDoc::new(7, 8, true);
            thread_doc.set_receipt_signing_key(SIGNING_SEED);

            // The approving identity is bound to the thread doc's editor cell.
            let approver = author_of_editor(thread_doc.editor_id());

            let mut pr = clean_pr();
            // The merge REQUIRES an approval: bind the check to the exact
            // approval turn the reviewer is about to post + the trusted key.
            let check = pr
                .review()
                .planned_approval_check(&thread_doc, "approved", vec![VERIFYING_KEY])
                .expect("the approval turn has a projection delta");
            pr = pr.with_required_check(check);

            // The landing document (the PR's code region — a cap-holding merger).
            let mut land_doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
            let pre = land_doc.state_commitment();

            // POLE 1: no approval yet → the merge is REFUSED, code untouched.
            match pr.land(&mut land_doc) {
                Err(PullRequestError::CheckNotSatisfied { check, reason }) => {
                    assert_eq!(check.as_str(), "approved");
                    assert!(matches!(reason, CheckRefusal::NoWitness), "{reason:?}");
                }
                other => panic!("expected CheckNotSatisfied, got {other:?}"),
            }
            assert_eq!(land_doc.state_commitment(), pre, "no merge turn ran");

            // The reviewer approves — a committed, executor-signed receipt.
            let receipt = pr
                .approve(&mut thread_doc, approver)
                .expect("the approval posts");
            assert_eq!(receipt.finality, Finality::Final);
            assert!(
                receipt.executor_signature.is_some(),
                "the thread executor signed the approval receipt"
            );

            // POLE 2: present the approval as the check's witness → it verifies
            // (real Ed25519 over the exact named turn) and the merge lands.
            pr.present_witness("approved", CheckWitness::Receipt(receipt));
            pr.checks_satisfied()
                .expect("the approval receipt satisfies the required check");
            let receipts = pr.land(&mut land_doc).expect("an approved PR lands");
            assert!(!receipts.is_empty());
            assert_eq!(*land_doc.graph(), pr.merge().unwrap().graph);
            assert!(land_doc.commitment_matches_projection());
            assert_eq!(
                content(land_doc.graph()).to_marked_string(),
                "two\nthree\n",
                "both sides' edits landed"
            );

            // The approval is attributable + immutable in the thread — bound to
            // the authenticated approver editor cell.
            let approvals = pr.review().approvals(&thread_doc);
            assert_eq!(approvals.len(), 1);
            assert_eq!(approvals[0].author, approver);
        }
    }
}
