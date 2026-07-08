//! The PULL REQUEST — review-as-stitcher, the first slice of the dregg-native
//! code forge (docs/deos/DREGG-FORGE.md) where the patch theory IS the version
//! control.
//!
//! A [`PullRequest`] is a proposed fork: a `head` [`History`] offered against a
//! target `base` [`History`] that share a prefix (their [`merge_base`]) and then
//! diverge. Nothing here is new machinery — the object WELDS the primitives the
//! crate already carries:
//!
//! - **The diff/conflict view** is [`three_way`] + [`render_three_way`]: the
//!   pushout of the two folds, with every conflict shown against the BASE column
//!   (the merge-base content both sides forked from). Empty ⇒ the PR is clean.
//! - **Review is resolution**: a reviewer settles a [`crate::ConflictRegion`]
//!   with a ready [`ResolutionChoice`] (`resolve_keep` / `resolve_connect` /
//!   `resolve_field` under the hood — resolution is *just another patch*,
//!   recorded into the PR's resolution set and authored by the resolver).
//! - **Merge is the stitch**: [`PullRequest::merge`] is refused
//!   ([`PullRequestError::UnresolvedConflict`]) while any conflict stands; once
//!   clean it yields the merged [`DocGraph`] plus the exact landing patch set —
//!   the head's suffix past the merge base followed by the resolutions, i.e.
//!   [`History::stitch`]'s append with the review baked in.
//! - **Landing is cap-gated through the REAL executor** (`substrate` feature):
//!   [`PullRequest::land`] drives each landing patch through
//!   [`ExecutorDrivenDoc::edit`] — the crate's sole executor entry, where
//!   `TurnExecutor::execute`'s `check_cross_cell_permission` gate runs. A merger
//!   holding the base region's edit cap lands finalized, journaled,
//!   receipt-chained turns; a NON-holder is refused in-band with
//!   `TurnError::CapabilityNotHeld` on the FIRST turn (so nothing lands — the
//!   cap is per `(editor, region)` and every landing turn targets the same
//!   region). No parallel gate exists here.
//! - **CI is receipted turns** (`substrate`): a PR can carry
//!   [`RequiredCheck`]s ([`crate::check`]); [`PullRequest::land`] verifies
//!   EVERY one against its presented witness (a committed, executor-signed
//!   check-turn receipt / a verified `ProofCondition` proof — never a bool)
//!   BEFORE driving any merge turn, refusing with
//!   [`PullRequestError::CheckNotSatisfied`] otherwise. No trusted CI runner:
//!   the proof IS the pass. Checks and caps are independent gates — both
//!   required.
//!
//! ## Named seams (deferred, not holes)
//!
//! - **The federated forge-grain**: this PR object is in-process; hosting PRs as
//!   grain/cell service objects (open/review/land across identities and nodes,
//!   quorum finality) is the forge's next slice.
//! - **The review-thread surface**: comments/approvals as document atoms on the
//!   PR itself (a PR is a document too) — not yet built; today the review record
//!   is the resolution patch set.
//! - **Atomic multi-patch landing**: [`PullRequest::land`] drives one finalized
//!   turn per landing patch (each turn atomic, the run receipt-chained). A cap
//!   refusal is all-or-nothing (it hits the first turn); folding the whole
//!   landing set into ONE multi-action turn is a small executor_drive extension,
//!   deferred.
//! - **Non-monotone supersede across the fork**: a *superseding* `SetField` in
//!   the head suffix collapses base-side assignments it never saw when replayed
//!   onto base (the standard patch-theory order-sensitivity of the non-monotone
//!   op); the monotone grammar (`Add`/`Delete`/`Connect`/fresh `SetField`) is
//!   order-independent and is what the pushout equality below is stated over.

use crate::atom::{Author, PatchId};
use crate::content::content;
use crate::graph::DocGraph;
use crate::history::History;
use crate::patch::Patch;
use crate::resolution::{RegionResolutions, ResolutionChoice, resolutions};
use crate::threeway::{ThreeWayConflict, merge_base, render_three_way, three_way};

#[cfg(feature = "substrate")]
use crate::check::{CheckId, CheckRefusal, CheckWitness, RequiredCheck};
#[cfg(feature = "substrate")]
use crate::executor_drive::ExecutorDrivenDoc;
#[cfg(feature = "substrate")]
use crate::review::ReviewThread;
#[cfg(feature = "substrate")]
use dregg_turn::{TurnError, TurnReceipt};

/// Why a pull request could not merge / land.
#[derive(Debug)]
pub enum PullRequestError {
    /// The PR still carries unresolved conflicts (listed, three-way rendered
    /// against the merge base). Merge is REFUSED until each is settled by
    /// [`PullRequest::resolve`].
    UnresolvedConflict(Vec<ThreeWayConflict>),
    /// The landing target document is not at this PR's base fold — landing
    /// against a moved target would silently skew the stitch. Re-target the PR
    /// (open it against the target's current history) instead.
    #[cfg(feature = "substrate")]
    DocNotAtBase,
    /// The REAL executor refused a landing turn in-band — for a merger without
    /// the base region's edit cap this is `TurnError::CapabilityNotHeld` from
    /// `check_cross_cell_permission`, and nothing landed.
    #[cfg(feature = "substrate")]
    Refused(TurnError),
    /// CI AS RECEIPTED TURNS: a required check is not satisfied by a verified
    /// cryptographic witness (a committed executor-signed check-turn receipt /
    /// a verified [`dregg_turn::ProofCondition`] proof — see [`crate::check`]).
    /// The gate runs BEFORE any merge turn is driven, so nothing landed and
    /// the document is byte-untouched. Never satisfiable by a bool.
    #[cfg(feature = "substrate")]
    CheckNotSatisfied {
        /// The unsatisfied check's name.
        check: CheckId,
        /// Why its witness (or absence) failed verification.
        reason: CheckRefusal,
    },
    /// The driven landing set does NOT reproduce the reviewed pushout. For the
    /// monotone grammar the sequential drive equals `merge()`'s pushout by
    /// commutativity, but a superseding `SetField` in the head suffix is
    /// order-sensitive (see the module doc) and can collapse a concurrent
    /// base-side assignment the pushout would have preserved as a clash. Rather
    /// than commit a document that diverges from what the reviewer/CI saw
    /// (`MergeOutcome.graph`), landing is REFUSED. Defense-in-depth: the drive
    /// result must equal the reviewed pushout. The turns already committed are
    /// returned so the caller can see how far it got before the divergence.
    #[cfg(feature = "substrate")]
    DriveDivergedFromPushout(Vec<TurnReceipt>),
}

/// A clean (or fully reviewed) merge: the merged fold plus the exact patch set
/// that lands it on the base.
#[derive(Clone, Debug)]
pub struct MergeOutcome {
    /// The merged document: the pushout of both sides' folds
    /// ([`three_way`]) with the PR's resolutions applied.
    pub graph: DocGraph,
    /// The landing set, in order: the head's patches past the merge base, then
    /// the resolutions. Committing these onto the base history IS the stitch
    /// (each patch keeps its own author/identity — no squash, no re-authoring).
    pub patches: Vec<Patch>,
}

impl MergeOutcome {
    /// The merged history: `base` with the landing patches committed (the
    /// [`History::stitch`] view of this outcome).
    pub fn merged_history(&self, base: &History) -> History {
        let mut h = base.clone();
        for p in &self.patches {
            h.commit(p.clone());
        }
        h
    }
}

/// A proposed fork `head` against a target `base`, with the review (resolution
/// patches) it has accumulated. See the module docs for how each face welds to
/// an existing primitive.
#[derive(Clone, Debug)]
pub struct PullRequest {
    /// The target the PR proposes to land on.
    base: History,
    /// The proposed fork (shares a prefix with `base`, then diverges).
    head: History,
    /// The review record: resolution patches settling this PR's conflicts, in
    /// the order they were taken. Each is authored by its resolver and lands
    /// with the merge (resolution is just another patch).
    resolutions: Vec<Patch>,
    /// CI AS RECEIPTED TURNS: the checks this PR must pass before it can land.
    /// Each is satisfied only by a verified cryptographic witness at land time
    /// ([`crate::check::RequiredCheck::satisfied_by`]) — never a bool.
    #[cfg(feature = "substrate")]
    required: Vec<RequiredCheck>,
    /// The witnesses presented against the required checks (by check id, last
    /// presentation wins). Presenting records; VERIFICATION happens at land
    /// time — a bad witness refuses the landing, it is not laundered here.
    #[cfg(feature = "substrate")]
    witnesses: Vec<(CheckId, CheckWitness)>,
    /// THE REVIEW THREAD: comments + approvals as cryptographically-OWNED,
    /// receipted document atoms ([`crate::review`]). Its content is committed in
    /// a backing document (a region cell distinct from this PR's code) — the
    /// commenting cap is independent of the land cap; this holds the thread's
    /// linearization tip + the receipted-turn evidence of every post.
    #[cfg(feature = "substrate")]
    review: ReviewThread,
}

impl PullRequest {
    /// Open a pull request proposing `head` against `base`.
    pub fn open(base: History, head: History) -> Self {
        PullRequest {
            base,
            head,
            resolutions: Vec::new(),
            #[cfg(feature = "substrate")]
            required: Vec::new(),
            #[cfg(feature = "substrate")]
            witnesses: Vec::new(),
            #[cfg(feature = "substrate")]
            review: ReviewThread::new(),
        }
    }

    /// Require a check for landing (builder form): [`PullRequest::land`] will
    /// refuse with [`PullRequestError::CheckNotSatisfied`] until `check` is
    /// satisfied by a verified witness ([`PullRequest::present_witness`]).
    #[cfg(feature = "substrate")]
    pub fn with_required_check(mut self, check: RequiredCheck) -> Self {
        self.required.push(check);
        self
    }

    /// Require a check for landing (in-place form of
    /// [`PullRequest::with_required_check`]).
    #[cfg(feature = "substrate")]
    pub fn require_check(&mut self, check: RequiredCheck) {
        self.required.push(check);
    }

    /// The checks this PR must pass before it can land.
    #[cfg(feature = "substrate")]
    pub fn required_checks(&self) -> &[RequiredCheck] {
        &self.required
    }

    /// Present a witness against a required check (a committed check-turn
    /// receipt / a condition proof). Presenting RECORDS; verification happens
    /// at land time — presenting garbage does not "satisfy" anything, the
    /// landing gate refuses it with the verifier's reason. A later
    /// presentation for the same check supersedes an earlier one.
    #[cfg(feature = "substrate")]
    pub fn present_witness(&mut self, check: impl Into<CheckId>, witness: CheckWitness) {
        let id = check.into();
        self.witnesses.retain(|(c, _)| *c != id);
        self.witnesses.push((id, witness));
    }

    /// VERIFY every required check against its presented witness — the CI
    /// gate [`PullRequest::land`] runs before driving any merge turn. `Ok(())`
    /// iff EVERY required check is satisfied by a genuine cryptographic
    /// witness ([`RequiredCheck::satisfied_by`]); otherwise the first
    /// unsatisfied check's refusal, as [`PullRequestError::CheckNotSatisfied`].
    #[cfg(feature = "substrate")]
    pub fn checks_satisfied(&self) -> Result<(), PullRequestError> {
        for check in &self.required {
            let witness = self.witnesses.iter().find(|(c, _)| *c == check.id);
            let refusal = match witness {
                None => CheckRefusal::NoWitness,
                Some((_, w)) => match check.satisfied_by(w) {
                    Ok(()) => continue,
                    Err(r) => r,
                },
            };
            return Err(PullRequestError::CheckNotSatisfied {
                check: check.id.clone(),
                reason: refusal,
            });
        }
        Ok(())
    }

    /// The target history.
    pub fn base(&self) -> &History {
        &self.base
    }

    /// The proposed fork.
    pub fn head(&self) -> &History {
        &self.head
    }

    /// The common ancestor: the longest shared prefix of `base` and `head`
    /// (the point they diverged), as a replayable [`History`].
    pub fn merge_base(&self) -> History {
        merge_base(&self.base, &self.head)
    }

    /// The divergence: `(base_suffix, head_suffix)` — each side's patches past
    /// the merge base. The head suffix is what the PR proposes to land.
    pub fn divergence(&self) -> (&[Patch], &[Patch]) {
        let shared = self.merge_base().len();
        (
            &self.base.patches()[shared..],
            &self.head.patches()[shared..],
        )
    }

    /// The review record so far: the resolution patches taken on this PR.
    pub fn resolutions(&self) -> &[Patch] {
        &self.resolutions
    }

    /// The merged fold as it currently stands: the pushout of both sides
    /// ([`three_way`]) with the recorded resolutions applied. This is the graph
    /// the conflict view, the resolution menu, and (once clean) the merge all
    /// read.
    pub fn merged_graph(&self) -> DocGraph {
        let mb = self.merge_base();
        let mut g = three_way(&mb, &self.base, &self.head);
        for p in &self.resolutions {
            p.apply(&mut g);
        }
        g
    }

    /// The PR's outstanding conflicts, three-way rendered (each region's BASE
    /// column recovered from the merge-base fold via [`render_three_way`]).
    /// Empty ⇒ the PR is clean (mergeable). Resolutions already recorded are
    /// applied first, so a settled conflict no longer appears.
    pub fn conflicts(&self) -> Vec<ThreeWayConflict> {
        render_three_way(&self.merged_graph(), &self.merge_base().replay())
    }

    /// True iff the PR carries no outstanding conflict (clean, or every
    /// conflict has been settled by [`PullRequest::resolve`]).
    pub fn is_clean(&self) -> bool {
        self.conflicts().is_empty()
    }

    /// The review menu: for every outstanding conflict region, the one-click
    /// [`ResolutionChoice`]s a reviewer can take (keep-one / order-all /
    /// settle-the-field), each carrying a ready patch authored by `resolver`.
    /// A clean PR yields an empty menu (nothing is fabricated).
    pub fn resolution_choices(&self, resolver: Author) -> Vec<RegionResolutions> {
        let g = self.merged_graph();
        let rendered = content(&g);
        resolutions(&g, &rendered, resolver)
    }

    /// REVIEW-AS-STITCHER: take a resolution choice on this PR, recording its
    /// ready patch into the PR's resolution set. Returns the resolution patch's
    /// content-addressed id. The conflict it settles disappears from
    /// [`PullRequest::conflicts`]; the patch lands with the merge, authored by
    /// the resolver who took it.
    pub fn resolve(&mut self, choice: &ResolutionChoice) -> PatchId {
        self.resolve_with(choice.patch.clone())
    }

    /// Low-level review: record an arbitrary resolution patch (resolution is
    /// just another patch — a hand-built `resolve_connect`/`resolve_keep_in`/
    /// `resolve_field` works exactly like a menu choice).
    pub fn resolve_with(&mut self, patch: Patch) -> PatchId {
        let id = patch.id();
        self.resolutions.push(patch);
        id
    }

    /// MERGE — produce the merged graph and the landing patch set.
    ///
    /// Refused with [`PullRequestError::UnresolvedConflict`] while any conflict
    /// stands; a clean (or fully resolved) PR yields the pushout-with-
    /// resolutions and the exact patches that land it (head suffix, then
    /// resolutions — each keeping its own author/identity).
    pub fn merge(&self) -> Result<MergeOutcome, PullRequestError> {
        let conflicts = self.conflicts();
        if !conflicts.is_empty() {
            return Err(PullRequestError::UnresolvedConflict(conflicts));
        }
        let (_, head_suffix) = self.divergence();
        let mut patches: Vec<Patch> = head_suffix.to_vec();
        patches.extend(self.resolutions.iter().cloned());
        Ok(MergeOutcome {
            graph: self.merged_graph(),
            patches,
        })
    }

    /// LAND — the merge as cap-gated, finalized, journaled turns through the
    /// REAL executor.
    ///
    /// `doc` is the live base document ([`ExecutorDrivenDoc`], its witness graph
    /// at this PR's base fold — see [`ExecutorDrivenDoc::new_at`]); its editor
    /// is the MERGER. Each landing patch is driven through
    /// [`ExecutorDrivenDoc::edit`] — the crate's sole `TurnExecutor::execute`
    /// entry, where `check_cross_cell_permission` gates every cross-cell
    /// `SetField`:
    ///
    /// - a merger HOLDING the base region's edit cap lands the whole set as
    ///   finalized (`Finality::Final`), receipt-chained turns;
    /// - a merger WITHOUT it is refused IN-BAND on the first turn
    ///   ([`PullRequestError::Refused`] wrapping `TurnError::CapabilityNotHeld`)
    ///   and nothing lands (the executor rolled back; the witness graph rolled
    ///   back with it).
    ///
    /// An unresolved PR never reaches the executor
    /// ([`PullRequestError::UnresolvedConflict`] first). A landing patch whose
    /// projection delta is empty (a no-op at the committed map) is skipped, not
    /// an error.
    ///
    /// **CI AS RECEIPTED TURNS**: every [`RequiredCheck`] must be satisfied by
    /// a VERIFIED cryptographic witness ([`PullRequest::checks_satisfied`])
    /// before any merge turn is driven — an unsatisfied check refuses with
    /// [`PullRequestError::CheckNotSatisfied`] and the document/ledger is
    /// byte-untouched (the merge never ran). The gate ordering is
    /// conflicts → doc-at-base → REQUIRED CHECKS → the executor's cap gate
    /// (in-band, per driven turn); checks and caps are INDEPENDENT — a
    /// satisfied check set does not confer the region cap.
    #[cfg(feature = "substrate")]
    pub fn land(&self, doc: &mut ExecutorDrivenDoc) -> Result<Vec<TurnReceipt>, PullRequestError> {
        let outcome = self.merge()?;
        if *doc.graph() != self.base.replay() {
            return Err(PullRequestError::DocNotAtBase);
        }
        // THE CI GATE: verify every required check's witness BEFORE driving
        // any turn. The proof IS the pass — a committed executor-signed
        // check-turn receipt or a verified ProofCondition witness, never a
        // bool (crate::check).
        self.checks_satisfied()?;
        // The reviewed pushout (what the reviewer + CI saw). The drive below
        // must reproduce it exactly (see DriveDivergedFromPushout).
        let expected = outcome.graph;
        let mut receipts = Vec::new();
        for patch in outcome.patches {
            match doc.edit(patch) {
                Ok(receipt) => receipts.push(receipt),
                // An empty projection delta: the patch is a no-op at the
                // committed map (e.g. structure already present) — skip.
                Err(TurnError::EmptyForest) => continue,
                // The executor's in-band refusal (the cap gate, or any other
                // real refusal): stop and surface it. A cap refusal hits the
                // FIRST mutating turn (the cap is per (editor, region)), so
                // nothing has landed.
                Err(e) => return Err(PullRequestError::Refused(e)),
            }
        }
        // FAIL-CLOSED: the sequentially-driven document must equal the reviewed
        // pushout. A superseding SetField in the head suffix (order-sensitive)
        // can otherwise land a document that silently drops a base edit the
        // pushout preserved — refuse rather than commit a divergent result.
        if *doc.graph() != expected {
            return Err(PullRequestError::DriveDivergedFromPushout(receipts));
        }
        Ok(receipts)
    }

    /// The PR's REVIEW THREAD (comments + approvals as owned, receipted atoms).
    #[cfg(feature = "substrate")]
    pub fn review(&self) -> &ReviewThread {
        &self.review
    }

    /// The PR's review thread, mutably.
    #[cfg(feature = "substrate")]
    pub fn review_mut(&mut self) -> &mut ReviewThread {
        &mut self.review
    }

    /// POST A REVIEW COMMENT on this PR — an [`crate::Op::Add`] patch authored
    /// by `author`, driven as a cap-gated finalized turn through `thread_doc`
    /// (the review thread's backing region cell, distinct from the PR's code
    /// document). A reviewer without the thread's review cap is refused in-band
    /// ([`TurnError::CapabilityNotHeld`]) with the thread byte-untouched. See
    /// [`crate::ReviewThread::comment`].
    #[cfg(feature = "substrate")]
    pub fn comment(
        &mut self,
        thread_doc: &mut ExecutorDrivenDoc,
        author: Author,
        text: &str,
    ) -> Result<TurnReceipt, TurnError> {
        self.review.comment(thread_doc, author, text)
    }

    /// POST AN APPROVAL on this PR — a distinguished marker atom authored by
    /// `author`, on the same receipted-turn path as [`PullRequest::comment`].
    /// The committed, executor-signed approval receipt can satisfy a
    /// [`crate::check::RequiredCheck`] (approval-as-required-check — see
    /// [`crate::ReviewThread::planned_approval_check`]). See
    /// [`crate::ReviewThread::approve`].
    #[cfg(feature = "substrate")]
    pub fn approve(
        &mut self,
        thread_doc: &mut ExecutorDrivenDoc,
        author: Author,
    ) -> Result<TurnReceipt, TurnError> {
        self.review.approve(thread_doc, author)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{AtomId, Author};
    use crate::merge::merge;
    use crate::patch::Op;

    /// A shared two-atom history ("one\n" then "two\n"), returning it plus the
    /// two atom ids.
    fn shared_history() -> (History, AtomId, AtomId) {
        let mut h = History::new();
        let (s1, op1) = Patch::add(1, "one\n", AtomId::ROOT);
        let (s2, op2) = Patch::add(2, "two\n", s1);
        h.commit(Patch::by(Author(0), [op1]));
        h.commit(Patch::by(Author(0), [op2]));
        (h, s1, s2)
    }

    /// A clean PR: base tombstones "one\n", head appends "three\n" — disjoint,
    /// non-conflicting edits on a shared ancestor.
    fn clean_pr() -> PullRequest {
        let (shared, s1, s2) = shared_history();
        let mut base = shared.branch();
        base.commit(Patch::by(Author(1), [Op::Delete { id: s1 }]));
        let mut head = shared.branch();
        head.commit(Patch::by(Author(2), [Patch::add(3, "three\n", s2).1]));
        PullRequest::open(base, head)
    }

    /// A conflicting PR: base and head each insert a different line after the
    /// same anchor — a genuine antichain.
    fn conflicting_pr() -> PullRequest {
        let (shared, _s1, s2) = shared_history();
        let mut base = shared.branch();
        base.commit(Patch::by(Author(1), [Patch::add(10, "alpha\n", s2).1]));
        let mut head = shared.branch();
        head.commit(Patch::by(Author(2), [Patch::add(11, "beta\n", s2).1]));
        PullRequest::open(base, head)
    }

    // ── POLE 1 (pure): a clean PR merges to the pushout of BOTH sides ────────

    #[test]
    fn a_clean_pr_merges_the_pushout_of_both_sides() {
        let pr = clean_pr();

        // The merge base is the shared prefix; both sides diverged by one patch.
        assert_eq!(pr.merge_base().len(), 2);
        let (base_suffix, head_suffix) = pr.divergence();
        assert_eq!((base_suffix.len(), head_suffix.len()), (1, 1));

        // Clean: no conflicts, mergeable.
        assert!(pr.conflicts().is_empty());
        assert!(pr.is_clean());

        let outcome = pr.merge().expect("a clean PR merges");
        // The merged graph IS the pushout of the two folds.
        assert_eq!(
            outcome.graph,
            merge(&pr.base().replay(), &pr.head().replay()),
            "the merged graph is the pushout"
        );
        // BOTH sides' edits are present: base's tombstone of "one" took effect
        // AND head's "three" landed.
        let text = content(&outcome.graph).to_marked_string();
        assert_eq!(text, "two\nthree\n", "both sides' edits in the merge");

        // The landing set is the head suffix (no resolutions were needed), and
        // the stitched history replays to the same fold.
        assert_eq!(outcome.patches.len(), 1);
        let stitched = outcome.merged_history(pr.base());
        assert_eq!(stitched.replay(), outcome.graph, "stitch replays the merge");
    }

    // ── POLE 2 (pure): a conflicting PR is REFUSED until review resolves it ──

    #[test]
    fn a_conflicting_pr_is_refused_until_resolved_then_merges() {
        let mut pr = conflicting_pr();

        // The conflict surfaces as a three-way region: both sides visible, the
        // BASE column empty (a pure concurrent insert — the ancestor had
        // nothing at the fork).
        let conflicts = pr.conflicts();
        assert_eq!(conflicts.len(), 1, "one conflict region");
        assert!(!pr.is_clean());
        let region = &conflicts[0];
        assert_eq!(region.base_text, "", "pure concurrent insert");
        let side_texts: Vec<&str> = region.sides.iter().map(|s| s.text.as_str()).collect();
        assert!(side_texts.contains(&"alpha\n") && side_texts.contains(&"beta\n"));

        // MERGE IS REFUSED while the conflict stands.
        match pr.merge() {
            Err(PullRequestError::UnresolvedConflict(cs)) => assert_eq!(cs.len(), 1),
            other => panic!("expected UnresolvedConflict, got {other:?}"),
        }

        // REVIEW: take the keep-both ORDER choice off the menu (authored by the
        // reviewer, Author(3)).
        let menu = pr.resolution_choices(Author(3));
        assert_eq!(menu.len(), 1, "one region to review");
        let choice = menu[0]
            .choices
            .iter()
            .find(|c| c.keeps_all())
            .expect("an order (keep both) choice")
            .clone();
        pr.resolve(&choice);

        // Settled: clean, and the merge now succeeds with BOTH alternatives
        // (ordered) plus the shared prefix.
        assert!(pr.is_clean(), "the resolution settled the conflict");
        let outcome = pr.merge().expect("a resolved PR merges");
        let text = content(&outcome.graph).to_marked_string();
        assert!(
            text.contains("alpha\n") && text.contains("beta\n"),
            "order keeps both: {text:?}"
        );
        assert!(
            text.starts_with("one\ntwo\n"),
            "shared prefix intact: {text:?}"
        );
        assert!(!content(&outcome.graph).has_conflict());

        // The landing set = head suffix + the resolution patch, the resolution
        // authored by its resolver (the review record).
        assert_eq!(outcome.patches.len(), 2);
        assert_eq!(outcome.patches[1].author, Author(3));
        assert_eq!(pr.resolutions().len(), 1);
    }

    #[test]
    fn a_keep_resolution_also_settles_the_pr() {
        let mut pr = conflicting_pr();
        let menu = pr.resolution_choices(Author(3));
        // Keep the HEAD side ("beta") — reviewer picks one alternative.
        let keep_beta = menu[0]
            .choices
            .iter()
            .find(|c| !c.keeps_all() && c.label.contains("beta"))
            .expect("a keep-beta choice")
            .clone();
        pr.resolve(&keep_beta);

        assert!(pr.is_clean());
        let outcome = pr.merge().expect("merges after keep");
        let text = content(&outcome.graph).to_marked_string();
        assert!(
            text.contains("beta\n") && !text.contains("alpha\n"),
            "{text:?}"
        );
    }

    // ── the substrate poles: landing through the REAL executor ──────────────

    #[cfg(feature = "substrate")]
    mod landing {
        use super::*;
        use crate::executor_drive::ExecutorDrivenDoc;
        use dregg_turn::{Finality, TurnError};

        #[test]
        fn a_clean_pr_lands_as_finalized_cap_gated_turns() {
            let pr = clean_pr();
            // The merger HOLDS the base region's edit cap.
            let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
            let pre = doc.state_commitment();

            let receipts = pr.land(&mut doc).expect("a cap-holding merger lands");
            assert!(!receipts.is_empty());
            for r in &receipts {
                assert_eq!(
                    r.finality,
                    Finality::Final,
                    "each landing turn is a FINALIZED executor commit"
                );
                assert_eq!(r.agent, doc.editor_id(), "the merger drove the turn");
            }

            // The landed document IS the merge outcome; the commitment moved
            // and matches the projection (the executor wrote the real leaves).
            let outcome = pr.merge().unwrap();
            assert_eq!(*doc.graph(), outcome.graph, "the landed fold is the merge");
            assert_ne!(
                doc.state_commitment(),
                pre,
                "the merge moved the commitment"
            );
            assert!(doc.commitment_matches_projection());
            assert_eq!(
                content(doc.graph()).to_marked_string(),
                "two\nthree\n",
                "both sides' edits landed"
            );
        }

        #[test]
        fn an_unresolved_pr_never_reaches_the_executor_and_lands_after_review() {
            let mut pr = conflicting_pr();
            let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
            let pre = doc.state_commitment();

            // REFUSED before any turn: the document commitment did not move.
            match pr.land(&mut doc) {
                Err(PullRequestError::UnresolvedConflict(cs)) => assert_eq!(cs.len(), 1),
                other => panic!("expected UnresolvedConflict, got {other:?}"),
            }
            assert_eq!(doc.state_commitment(), pre, "no turn ran");

            // Review settles it; the landing then commits (head patch + the
            // resolution patch, receipt-chained).
            let menu = pr.resolution_choices(Author(3));
            let order = menu[0]
                .choices
                .iter()
                .find(|c| c.keeps_all())
                .unwrap()
                .clone();
            pr.resolve(&order);

            let receipts = pr.land(&mut doc).expect("a resolved PR lands");
            assert_eq!(receipts.len(), 2, "head patch + resolution patch");
            assert_eq!(
                receipts[1].previous_receipt_hash,
                Some(receipts[0].receipt_hash()),
                "the landing turns are receipt-chained"
            );
            assert_eq!(*doc.graph(), pr.merge().unwrap().graph);
            assert!(doc.commitment_matches_projection());
            assert!(!content(doc.graph()).has_conflict());
        }

        #[test]
        fn a_merger_without_the_region_cap_is_refused_in_band() {
            let pr = clean_pr();

            // The merger LACKS the base region's edit cap: the executor's
            // check_cross_cell_permission gate refuses the first landing turn
            // IN-BAND — no merge, document untouched.
            let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, false);
            let pre = doc.state_commitment();

            match pr.land(&mut doc) {
                Err(PullRequestError::Refused(TurnError::CapabilityNotHeld { actor, target })) => {
                    assert_eq!(actor, doc.editor_id(), "the merger is the refused actor");
                    assert_eq!(
                        target,
                        doc.region_id(),
                        "the base region is the gated target"
                    );
                }
                other => panic!("expected an in-band CapabilityNotHeld refusal, got {other:?}"),
            }
            assert_eq!(doc.state_commitment(), pre, "nothing landed");
            assert_eq!(
                *doc.graph(),
                pr.base().replay(),
                "the base fold is untouched"
            );
            assert!(doc.commitment_matches_projection());

            // WITH the cap, the same PR is admitted.
            let mut held = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
            let receipts = pr
                .land(&mut held)
                .expect("the cap-holding merger is admitted");
            assert!(!receipts.is_empty());
            assert_eq!(*held.graph(), pr.merge().unwrap().graph);
        }

        #[test]
        fn landing_against_a_moved_target_is_refused() {
            let pr = clean_pr();
            // The target document is NOT at the PR's base fold (it is at the
            // merge base only — the base suffix is missing).
            let mut doc = ExecutorDrivenDoc::new_at(&pr.merge_base().replay(), 1, 2, true);
            match pr.land(&mut doc) {
                Err(PullRequestError::DocNotAtBase) => {}
                other => panic!("expected DocNotAtBase, got {other:?}"),
            }
        }
    }

    // ── CI AS RECEIPTED TURNS: the required-check gate on landing ───────────

    #[cfg(feature = "substrate")]
    mod required_checks {
        use super::*;
        use crate::check::{CheckRefusal, CheckWitness, RequiredCheck};
        use crate::executor_drive::ExecutorDrivenDoc;
        use dregg_turn::{ConditionProof, Finality, ProofCondition, TurnError};

        /// RFC 8032 §7.1 TEST 1: a REAL Ed25519 (seed, verifying-key) pair —
        /// the executor derives its verifying key from the 32-byte seed by
        /// standard Ed25519 key generation, so this pubkey matches this seed.
        /// dregg-doc has no ed25519 dependency; the pair arrives as data (in
        /// the real forge, the trusted executor keys are repo policy).
        const CI_SIGNING_SEED: [u8; 32] = [
            0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec,
            0x2c, 0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03,
            0x1c, 0xae, 0x7f, 0x60,
        ];
        const CI_VERIFYING_KEY: [u8; 32] = [
            0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64,
            0x07, 0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68,
            0xf7, 0x07, 0x51, 0x1a,
        ];

        /// The CI job's own results document: a signing executor plus the
        /// check patch it will drive (writing the check's result line). The
        /// check turn's hash is PLANNED (named before it runs) — that hash is
        /// what the PR's required check binds to.
        fn ci_job() -> (ExecutorDrivenDoc, Patch, [u8; 32]) {
            let mut ci_doc = ExecutorDrivenDoc::new(7, 8, true);
            ci_doc.set_receipt_signing_key(CI_SIGNING_SEED);
            let check_patch = Patch::by(
                Author(9),
                [Patch::add(100, "check: build PASS\n", AtomId::ROOT).1],
            );
            let planned = ci_doc
                .planned_turn_hash(&check_patch)
                .expect("the check turn has a real projection delta");
            (ci_doc, check_patch, planned)
        }

        #[test]
        fn an_unsatisfied_required_check_refuses_the_landing_untouched_then_the_committed_receipt_lands_it()
         {
            let (mut ci_doc, check_patch, planned) = ci_job();

            // The PR requires the check BEFORE it has run: the required check
            // names the exact check turn (by planned hash) + the trusted
            // executor key that must have signed its receipt.
            let mut pr = clean_pr().with_required_check(RequiredCheck::committed_receipt(
                "build",
                planned,
                vec![CI_VERIFYING_KEY],
            ));

            let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
            let pre = doc.state_commitment();

            // POLE 1: no witness → REFUSED, and the document is BYTE-UNTOUCHED
            // (the merge never ran — no turn was driven).
            match pr.land(&mut doc) {
                Err(PullRequestError::CheckNotSatisfied { check, reason }) => {
                    assert_eq!(check.as_str(), "build");
                    assert!(matches!(reason, CheckRefusal::NoWitness), "{reason:?}");
                }
                other => panic!("expected CheckNotSatisfied, got {other:?}"),
            }
            assert_eq!(doc.state_commitment(), pre, "no turn ran");
            assert_eq!(*doc.graph(), pr.base().replay(), "base fold untouched");

            // RUN THE CHECK: drive the real check turn through the CI doc's
            // executor. The committed receipt IS the pass — finalized, and
            // executor-signed (the non-fabricable part).
            let receipt = ci_doc.edit(check_patch).expect("the check turn commits");
            assert_eq!(
                receipt.turn_hash, planned,
                "the plan named exactly the turn that ran"
            );
            assert_eq!(receipt.finality, Finality::Final);
            assert!(
                receipt.executor_signature.is_some(),
                "the CI executor signed the check receipt"
            );

            // POLE 2: the SAME PR with the committed receipt presented → the
            // check verifies (real Ed25519 over the canonical executor-signed
            // message) and the merge lands as finalized cap-gated turns.
            pr.present_witness("build", CheckWitness::Receipt(receipt));
            pr.checks_satisfied()
                .expect("the committed receipt satisfies");
            let receipts = pr.land(&mut doc).expect("a checked PR lands");
            assert!(!receipts.is_empty());
            for r in &receipts {
                assert_eq!(r.finality, Finality::Final);
            }
            assert_eq!(*doc.graph(), pr.merge().unwrap().graph);
            assert!(doc.commitment_matches_projection());
            assert_eq!(
                content(doc.graph()).to_marked_string(),
                "two\nthree\n",
                "both sides' edits landed"
            );
        }

        #[test]
        fn a_fabricated_or_tampered_check_receipt_never_satisfies() {
            let (mut ci_doc, check_patch, planned) = ci_job();
            let real = ci_doc.edit(check_patch).expect("the check turn commits");

            let check = |keys: Vec<[u8; 32]>| {
                clean_pr()
                    .with_required_check(RequiredCheck::committed_receipt("build", planned, keys))
            };
            let refusal_of = |pr: &PullRequest| match pr.checks_satisfied() {
                Err(PullRequestError::CheckNotSatisfied { reason, .. }) => reason,
                other => panic!("expected CheckNotSatisfied, got {other:?}"),
            };

            // An UNSIGNED copy of the real receipt: refused fail-closed (a
            // receipt struct anyone can populate; without a signature it
            // cannot witness a check).
            let mut unsigned = real.clone();
            unsigned.executor_signature = None;
            let mut pr = check(vec![CI_VERIFYING_KEY]);
            pr.present_witness("build", CheckWitness::Receipt(unsigned));
            assert!(matches!(refusal_of(&pr), CheckRefusal::Unsigned));

            // A TAMPERED signature: real Ed25519 verification fails.
            let mut tampered = real.clone();
            if let Some(sig) = tampered.executor_signature.as_mut() {
                sig[0] ^= 0x01;
            }
            let mut pr = check(vec![CI_VERIFYING_KEY]);
            pr.present_witness("build", CheckWitness::Receipt(tampered));
            assert!(matches!(refusal_of(&pr), CheckRefusal::SignatureUnverified));

            // A receipt signed by an UNTRUSTED executor (wrong trusted key
            // set): refused — no trusted-runner laundering.
            let mut wrong_key = [0u8; 32];
            wrong_key[0] = 0xAA;
            let mut pr = check(vec![wrong_key]);
            pr.present_witness("build", CheckWitness::Receipt(real.clone()));
            assert!(matches!(refusal_of(&pr), CheckRefusal::SignatureUnverified));

            // A receipt for a DIFFERENT turn (a real committed one, even):
            // refused — the check names the exact check turn.
            let other_patch = Patch::by(
                Author(9),
                [Patch::add(101, "some other job\n", AtomId::ROOT).1],
            );
            let other = ci_doc.edit(other_patch).expect("another turn commits");
            assert!(other.executor_signature.is_some());
            let mut pr = check(vec![CI_VERIFYING_KEY]);
            pr.present_witness("build", CheckWitness::Receipt(other));
            assert!(matches!(refusal_of(&pr), CheckRefusal::WrongTurn { .. }));

            // The genuine article still satisfies (the poles are about the
            // witness, not the gate being stuck closed).
            let mut pr = check(vec![CI_VERIFYING_KEY]);
            pr.present_witness("build", CheckWitness::Receipt(real));
            pr.checks_satisfied()
                .expect("the real signed receipt passes");
        }

        #[test]
        fn a_proof_condition_check_is_satisfied_only_by_the_real_witness() {
            // The check is a ProofCondition (HashPreimage): satisfied only by
            // revealing the actual preimage, verified through the REAL
            // dregg_turn::resolve_condition path.
            let preimage: [u8; 32] = [0x42; 32];
            let hash: [u8; 32] = *blake3::hash(&preimage).as_bytes();
            let mut pr = clean_pr().with_required_check(RequiredCheck::condition(
                "release-key",
                ProofCondition::HashPreimage { hash },
            ));

            let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
            let pre = doc.state_commitment();

            // No witness → refused, untouched.
            match pr.land(&mut doc) {
                Err(PullRequestError::CheckNotSatisfied { check, reason }) => {
                    assert_eq!(check.as_str(), "release-key");
                    assert!(matches!(reason, CheckRefusal::NoWitness));
                }
                other => panic!("expected CheckNotSatisfied, got {other:?}"),
            }
            assert_eq!(doc.state_commitment(), pre);

            // A WRONG preimage → still refused (verification, not presence).
            pr.present_witness(
                "release-key",
                CheckWitness::Condition(ConditionProof::Preimage([0x13; 32])),
            );
            match pr.land(&mut doc) {
                Err(PullRequestError::CheckNotSatisfied { reason, .. }) => {
                    assert!(
                        matches!(reason, CheckRefusal::ConditionUnsatisfied(_)),
                        "{reason:?}"
                    );
                }
                other => panic!("expected CheckNotSatisfied, got {other:?}"),
            }
            assert_eq!(doc.state_commitment(), pre, "still no turn ran");

            // The REAL preimage → the condition verifies and the PR lands.
            pr.present_witness(
                "release-key",
                CheckWitness::Condition(ConditionProof::Preimage(preimage)),
            );
            let receipts = pr.land(&mut doc).expect("the witnessed PR lands");
            assert!(!receipts.is_empty());
            assert_eq!(*doc.graph(), pr.merge().unwrap().graph);
            assert!(doc.commitment_matches_projection());
        }

        #[test]
        fn checks_and_caps_are_independent_gates() {
            // A fully satisfied check set does NOT confer the region cap: a
            // capless merger is still refused in-band by the executor.
            let (mut ci_doc, check_patch, planned) = ci_job();
            let receipt = ci_doc.edit(check_patch).expect("the check turn commits");

            let mut pr = clean_pr().with_required_check(RequiredCheck::committed_receipt(
                "build",
                planned,
                vec![CI_VERIFYING_KEY],
            ));
            pr.present_witness("build", CheckWitness::Receipt(receipt));
            pr.checks_satisfied().expect("the check IS satisfied");

            // The merger LACKS the base region's edit cap.
            let mut capless = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, false);
            let pre = capless.state_commitment();
            match pr.land(&mut capless) {
                Err(PullRequestError::Refused(TurnError::CapabilityNotHeld { .. })) => {}
                other => panic!("expected the cap refusal, got {other:?}"),
            }
            assert_eq!(capless.state_commitment(), pre, "nothing landed");

            // And the cap alone is not enough without the check: strip the
            // witness, hold the cap → the CHECK gate refuses first.
            let mut unchecked = pr.clone();
            unchecked.witnesses.clear();
            let mut held = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
            match unchecked.land(&mut held) {
                Err(PullRequestError::CheckNotSatisfied { .. }) => {}
                other => panic!("expected CheckNotSatisfied, got {other:?}"),
            }

            // Both gates open → lands.
            let receipts = pr.land(&mut held).expect("check + cap → lands");
            assert!(!receipts.is_empty());
        }
    }
}
