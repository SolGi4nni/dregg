//! # `dreggnet-doc` — the COLLABORATIVE DOCUMENT offering.
//!
//! The dungeon is offering #0 (a confined narrative world). This is the
//! **productivity/collaboration** one, and it is the same five-part shape:
//!
//! 1. **A per-session confined thing** — one live shared document (a real
//!    `dregg_cell::Cell`, committed over its `fields_root`).
//! 2. **Real verifiable turns** — an EDIT is one real
//!    [`dregg_turn::TurnExecutor::execute`] turn through the document substrate's
//!    executor entry ([`dregg_doc::MultiEditorDoc::edit`]), landing a genuine
//!    finalized [`TurnReceipt`] on the editing collaborator's own per-agent chain.
//! 3. **The referee is the executor + the document soundness core, never prose** —
//!    an *unauthorized* edit (an actor without the region's edit cap) is refused
//!    **in-band by the executor** (`TurnError::CapabilityNotHeld`); a *conflicting*
//!    edit (one that would leave the document carrying an unresolved antichain or
//!    field clash) is refused by `dregg-doc`'s own conflict semantics. Nothing
//!    commits on a refusal (the anti-ghost tooth).
//! 4. **Payment-gated** — [`Offering::price`] names a per-edit [`RunCost`]
//!    (free tier by default; a resolution is always free).
//! 5. **Verifiable end to end** — [`Offering::verify`] re-drives the WHOLE edit
//!    chain from genesis through the real executor and checks that the document
//!    reproduces, byte for byte, at every step. A forged edit fails.
//!
//! ## What is consumed, and what is NOT re-implemented
//!
//! Every document semantic comes from [`dregg_doc`] — the Pijul-shaped patch
//! theory (`DocGraph` / `Patch` / `Op` / `History`), the categorical merge
//! (`merge` = the pushout as a total graph union), the conflict model
//! (`content`'s first-class antichain / field-clash [`ConflictRegion`]s + the
//! two-regime [`Regime`] classifier), provenance/blame, and the executor-drive
//! seam ([`MultiEditorDoc`], where a per-region edit cap is a c-list capability
//! the executor's `check_cross_cell_permission` gate enforces). This crate adds
//! **no CRDT, no merge rule, no conflict rule** of its own: it is the *session +
//! affordance + verification* layer that presents the substrate as an
//! [`Offering`].
//!
//! ## The session model (the deep model — N real per-agent chains over ONE ledger)
//!
//! A [`DocSession`] holds **one** [`dregg_doc::MultiEditorDoc`] — N distinct editor
//! cells (distinct agents), each optionally holding the shared region cell's edit
//! cap, all driving turns through **one** `TurnExecutor` over **one** `Ledger`.
//! Because the executor keys the receipt-chain head (`previous_receipt_hash`) and
//! the agent nonce by *cell id*, each collaborator keeps their **real cross-edit
//! per-agent chain**: collaborator A's second edit chains off A's own first, with
//! A's nonce monotone, even when B edited in between. The session no longer
//! re-bases a fresh single-editor document per edit (which restarted every actor at
//! nonce 0 with no `previous_receipt_hash`); the per-agent chain is now the genuine
//! executor chain, not a document-commitment shadow of it.
//!
//! The session also holds the document's [`History`] (the patch chain — the document
//! IS its history), an ordered roster of collaborators (each with a [`Role`], which
//! decides whether their editor cell holds the region's edit capability), and the
//! [`CommittedEdit`] log — one entry per landed turn, binding the turn's
//! deterministic core (`turn_hash` / `effects_hash` / pre- and post-state roots) and
//! the document's commitment after it. The `turn_hash` transitively binds the
//! editor's prior receipt hash (via `Turn::previous_receipt_hash`), so a
//! spliced/reordered chain moves the turn hash and breaks replay.
//!
//! Two workarounds the earlier single-editor model carried are now **retired**:
//! - **The per-agent chain is real** (was: re-based per edit). The session drives
//!   [`MultiEditorDoc::edit`] with the editing collaborator's slot, so their nonce
//!   and receipt chain advance across the session — [`DocSession::editor_chain`]
//!   exposes it, and replay reconstructs it identically (the executor's default
//!   timestamp is `0`, so every receipt hash is deterministic and reproducible).
//! - **An edit's prose rides [`Action::text`]** (was: on [`Action::label`]). A
//!   document edit's inserted text / a title's new value is a first-class string
//!   payload on the affordance, round-tripped losslessly through a [`Frontend`]'s
//!   present/collect — the affordance's `label` is now purely the human prompt.
//!
//! - **The conflict gate is the fold, not `PullRequest::merge`.** A live session is
//!   the *fast-forward* case (the new history is the old history plus one patch), so
//!   the session gates each 1-patch edit on the FOLD of the new history with
//!   dregg-doc's own detector ([`content`] + [`Regime`]) — the same detector
//!   `PullRequest::conflicts` reads. dregg-doc's `three_way` now honors its base, so
//!   `PullRequest`'s pushout also lands a superseding resolution on a fast-forward
//!   (`tests/driven.rs` pins it); the `PullRequest` path stays the right thing for a
//!   genuine *fork* (a review branch).
//!
//! ## What a fuller collaborative document still adds (named honestly)
//!
//! - **Concurrent divergent replicas.** Here edits are *sequenced* through one
//!   executor (one node, one linear ledger fold). True concurrent authoring (two
//!   editors composing on divergent replicas, then a branch-and-stitch merge) is the
//!   patch algebra's job (`dregg_doc::merge` / the two-device-sync path), layered
//!   ABOVE this — each replica a `MultiEditorDoc`, the stitch a further turn.
//! - **The review-branch PR path as an offering surface.** `three_way` is fixed and
//!   a fork's merge lands; wiring `dregg_doc::review` (threaded comments + approvals
//!   as receipted atoms) and `PullRequest` into a *review* affordance surface is the
//!   next offering, not this one.
//! - **Rich inline marks** (`dregg_doc::marks`), **presence / cursors** (ephemeral,
//!   no substrate analogue), and **character-level granularity** (`Doc::edit`'s token
//!   LCS; this offering's edits are span-level `Add`/`Delete`, the substrate's own
//!   atom granularity) round out the surface.

use std::collections::BTreeMap;

use deos_view::{MenuItem, ViewNode};
use dregg_doc::{
    AtomId, Author, ConflictRegion, DocGraph, History, MultiEditorDoc, Op, Patch, Regime, Rendered,
    content, walk_atoms,
};
use dregg_turn::{TurnError, TurnReceipt};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify, RunCost, SessionConfig,
    Surface, VerifyReport,
};

/// The deterministic Ed25519 signing seed the session equips its shared executor
/// with: every committed edit (from any collaborator) carries a genuine
/// `executor_signature`, so each editor's per-agent chain is a chain of
/// NON-FABRICABLE witnesses (verifiable via
/// [`dregg_turn::verify_receipt_signature_with_keys`] against the verifying key
/// this seed derives). It is a fixed constant so replay re-derives the same
/// signatures — the seam stays deterministic.
pub const RECEIPT_SIGNING_SEED: [u8; 32] = [0x5c; 32];

/// Insert a text span into the document, ordered after the anchor named by
/// [`Action::arg`] (see [`DocSession::anchors`]). The span's TEXT is the action's
/// first-class [`Action::text`] payload. Desugars to `dregg_doc::Op::Add`.
pub const TURN_INSERT: &str = "insert";
/// Tombstone the live cell named by [`Action::arg`] (1-based over
/// [`DocSession::cells`]). Desugars to `dregg_doc::Op::Delete` — a monotone
/// tombstone, never a physical removal (the atom survives for provenance).
pub const TURN_DELETE: &str = "delete";
/// Assign the document's single-valued `title` field (the non-monotone fragment).
/// The VALUE is the action's [`Action::text`] payload. Desugars to a
/// **non-superseding** `dregg_doc::Op::SetField` — a second, differing assignment is
/// a real [`Regime::Field`] clash, and is refused.
pub const TURN_SET_TITLE: &str = "set_title";
/// **Resolve** a `title` clash by settling it: a **superseding**
/// `dregg_doc::Op::SetField` that collapses the whole assignment set to the chosen
/// value ([`Action::text`]). This is the "a conflict is a first-class state a later
/// patch resolves" face — and it is always [`RunCost::free`].
pub const TURN_RESOLVE_TITLE: &str = "resolve_title";
/// **Resolve** a prose antichain by ORDERING it: `Connect(a, b)` — "a comes before
/// b" — collapsing the antichain into a chain. [`Action::arg`] is the index of the
/// conflict region (0-based over [`DocSession::conflicts`]); the alternatives are
/// ordered in the region's canonical order. Desugars to `dregg_doc::Op::Connect`.
pub const TURN_ORDER_CONFLICT: &str = "order_conflict";

/// The document's single-valued title field (the non-monotone/authority fragment
/// the [`Regime::Field`] classifier guards).
pub const FIELD_TITLE: &str = "title";

/// A collaborator's role — and therefore whether their editor cell holds the
/// document region's **edit capability**.
///
/// This is not a decoration: [`Role::Editor`] grants a real c-list capability to
/// the region cell, and [`Role::Commenter`] does not — so a commenter's edit turn
/// is refused **by the executor** (`check_cross_cell_permission` →
/// `TurnError::CapabilityNotHeld`), in-band, with nothing committed. An actor who
/// is not on the roster at all is treated as an outsider: same gate, same refusal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// Holds the region's edit cap — their edits commit.
    Editor,
    /// Does NOT hold the region's edit cap — the executor refuses their edits.
    /// (Read/comment affordances are the fuller-collaboration seam; see the crate
    /// docs.)
    Commenter,
}

impl Role {
    /// Whether this role's editor cell is granted the region's edit capability.
    pub fn holds_edit_cap(self) -> bool {
        matches!(self, Role::Editor)
    }

    /// A short label for the surface.
    pub fn label(self) -> &'static str {
        match self {
            Role::Editor => "editor",
            Role::Commenter => "commenter (no edit cap)",
        }
    }
}

/// A roster entry: who, their [`Role`], and the deterministic **editor-cell seed**
/// their turns are signed from. The seed is the roster index + 1, so it is stable
/// under replay (the verifier re-derives the same editor cell — hence the same
/// agent, the same ledger roots, the same `turn_hash`).
#[derive(Debug, Clone)]
pub struct Collaborator {
    /// The frontend-agnostic identity.
    pub who: DreggIdentity,
    /// Editor (holds the region edit cap) or commenter (does not).
    pub role: Role,
    /// The deterministic editor-cell seed (roster index + 1).
    pub seed: u8,
}

/// The seed an actor who is NOT on the roster gets: a real editor cell, with **no**
/// region capability — so an outsider's edit reaches the executor and is refused
/// there (not pre-filtered by us). One shared outsider slot serves every outsider:
/// an outsider never holds the cap, so their edit never commits and no per-agent
/// chain state accumulates on the slot.
const OUTSIDER_SEED: u8 = 200;

/// **One landed edit** — the record of a real committed turn.
///
/// It binds the *deterministic core* of the executor's receipt: the `turn_hash`
/// (the turn the executor admitted — which transitively binds the editor's prior
/// receipt hash via `previous_receipt_hash`), the `effects_hash` (the `SetField`
/// writes it applied), and the pre/post ledger state roots. It deliberately does
/// NOT bind `TurnReceipt::receipt_hash()` directly: the receipt hash is
/// reproducible here (the executor's timestamp defaults to `0`), and the chain
/// linkage it carries is already pinned through `turn_hash`.
#[derive(Debug, Clone)]
pub struct CommittedEdit {
    /// Who made the edit.
    pub actor: DreggIdentity,
    /// The document patch it committed (the real `dregg_doc::Patch`).
    pub patch: Patch,
    /// The genuine turn hash the executor admitted.
    pub turn_hash: [u8; 32],
    /// The genuine effects hash (the kernel writes).
    pub effects_hash: [u8; 32],
    /// The ledger state root before the turn.
    pub pre_state_hash: [u8; 32],
    /// The ledger state root after the turn.
    pub post_state_hash: [u8; 32],
    /// The DOCUMENT's commitment after this edit — the region cell's canonical
    /// state commitment (which absorbs `fields_root`, the digest of the document
    /// projection the executor wrote). This is the chain a light client follows.
    pub doc_commitment: [u8; 32],
}

/// The **public, transmissible record** of a document session — what a frontend
/// serializes, transmits, persists, and might receive back FORGED. The
/// [`RecordVerify`] seam re-checks it against the session's authentic identity
/// (the private region seed + the roster, which never leave the offering).
#[derive(Debug, Clone)]
pub struct DocRecord {
    /// Every landed edit, in order.
    pub edits: Vec<CommittedEdit>,
    /// The document's commitment at the end of the chain.
    pub commitment: [u8; 32],
}

/// **A live collaborative document session** over the real `dregg-doc` substrate.
///
/// The document IS its patch history ([`History`]); the current content is the fold
/// ([`MultiEditorDoc::graph`]). Every landed edit is one real executor turn on the
/// editing collaborator's own per-agent chain; the [`CommittedEdit`] log is the
/// chain [`Offering::verify`] re-drives.
pub struct DocSession {
    /// The document (region) cell's deterministic seed — the session's private
    /// world identity. A verifier re-derives the SAME region cell from it, so a
    /// forged record cannot re-target another document.
    region_seed: u8,
    /// The collaborators, in invitation order (the index fixes each one's editor
    /// slot in `doc` + its cell seed, so replay reproduces the same agents).
    roster: Vec<Collaborator>,
    /// The conflict policy (copied from the offering at `open`), so the session can
    /// re-drive its own edits on a roster change without the offering in hand.
    policy: ConflictPolicy,
    /// **The one shared collaborative document** — N editor cells (roster + a shared
    /// outsider slot) over one region ledger. Each committed edit advances its
    /// editing collaborator's per-agent nonce + receipt chain; the others are
    /// untouched.
    doc: MultiEditorDoc,
    /// The document's patch history — the document, as its edits.
    history: History,
    /// One entry per landed turn.
    edits: Vec<CommittedEdit>,
}

impl DocSession {
    /// Invite `who` with `role` — assigning them a deterministic editor cell.
    /// A [`Role::Editor`] is granted the document region's edit capability (their
    /// turns commit); a [`Role::Commenter`] is not (the executor refuses their
    /// edits). Re-inviting an existing collaborator UPDATES their role and keeps
    /// their cell. The shared document is rebuilt so the new editor slot (and its
    /// cap) is live; any already-committed edits are re-driven onto the fresh
    /// ledger (deterministically reproducing each collaborator's chain).
    pub fn invite(&mut self, who: DreggIdentity, role: Role) {
        if let Some(existing) = self.roster.iter_mut().find(|c| c.who == who) {
            existing.role = role;
        } else {
            let seed = (self.roster.len() as u8).saturating_add(1);
            self.roster.push(Collaborator { who, role, seed });
        }
        self.rebuild();
    }

    /// The roster, in invitation order.
    pub fn roster(&self) -> &[Collaborator] {
        &self.roster
    }

    /// `who`'s role, or `None` if they are not on the roster (an outsider).
    pub fn role_of(&self, who: &DreggIdentity) -> Option<Role> {
        self.roster.iter().find(|c| c.who == *who).map(|c| c.role)
    }

    /// The editor-slot indices used to construct `doc`: roster order, then one
    /// shared outsider slot at the end. Slot `i` (`i < roster.len()`) is
    /// `roster[i]`; slot `roster.len()` is the outsider.
    fn slots(&self) -> Vec<(u8, bool)> {
        let mut out: Vec<(u8, bool)> = self
            .roster
            .iter()
            .map(|c| (c.seed, c.role.holds_edit_cap()))
            .collect();
        out.push((OUTSIDER_SEED, false));
        out
    }

    /// The `doc` editor-slot index `who` drives their turn with. A roster member's
    /// slot is their invitation index; an outsider drives the shared outsider slot
    /// (no cap — their edit reaches the executor and is refused there).
    fn slot_of(&self, who: &DreggIdentity) -> usize {
        self.roster
            .iter()
            .position(|c| c.who == *who)
            .unwrap_or(self.roster.len())
    }

    /// The editor-cell seed `who`'s patch is authored from (the `Author` label).
    fn seed_of(&self, who: &DreggIdentity) -> u8 {
        self.roster
            .iter()
            .find(|c| c.who == *who)
            .map(|c| c.seed)
            .unwrap_or(OUTSIDER_SEED)
    }

    /// Build a fresh signed [`MultiEditorDoc`] for the current roster.
    fn fresh_doc(&self) -> MultiEditorDoc {
        let mut doc = MultiEditorDoc::new(self.region_seed, &self.slots());
        doc.set_receipt_signing_key(RECEIPT_SIGNING_SEED);
        doc
    }

    /// Rebuild the shared document for the current roster, re-driving every
    /// already-committed edit onto the fresh ledger. Driving is deterministic, so
    /// each collaborator's per-agent chain is reproduced identically; the
    /// [`CommittedEdit`] log's state roots are regenerated to the (possibly wider)
    /// editor set so the record stays self-consistent with what [`Offering::verify`]
    /// re-drives. An edit that no longer re-drives (e.g. an editor downgraded to a
    /// commenter after they edited) is dropped — it genuinely no longer commits.
    fn rebuild(&mut self) {
        let mut doc = self.fresh_doc();
        let prior = std::mem::take(&mut self.edits);
        let mut history = History::new();
        let mut edits = Vec::new();
        for e in prior {
            let slot = self.slot_of(&e.actor);
            if let Ok(landed) = drive_on(&mut doc, slot, &e.patch, self.policy) {
                history.commit(e.patch.clone());
                edits.push(CommittedEdit {
                    actor: e.actor,
                    patch: e.patch,
                    turn_hash: landed.receipt.turn_hash,
                    effects_hash: landed.receipt.effects_hash,
                    pre_state_hash: landed.receipt.pre_state_hash,
                    post_state_hash: landed.receipt.post_state_hash,
                    doc_commitment: landed.doc_commitment,
                });
            }
        }
        self.doc = doc;
        self.history = history;
        self.edits = edits;
    }

    /// The document's patch history (the document, as its edits).
    pub fn history(&self) -> &History {
        &self.history
    }

    /// The current fold — the live shared document graph.
    pub fn graph(&self) -> &DocGraph {
        self.doc.graph()
    }

    /// The landed-edit log (one entry per committed turn).
    pub fn edits(&self) -> &[CommittedEdit] {
        &self.edits
    }

    /// `who`'s **real per-agent receipt chain** over this session — the genuine
    /// executor chain that collaborator authored, in order (hash-linked by
    /// `previous_receipt_hash`, nonce-monotone from 0, each receipt carrying a
    /// verifiable executor signature). Empty for an actor who never committed (a
    /// commenter, an outsider). This is the guarantee the deep model buys: an
    /// editor's second edit chains off their OWN first even across another editor's
    /// interleaved edit.
    pub fn editor_chain(&self, who: &DreggIdentity) -> &[TurnReceipt] {
        self.doc.editor_chain(self.slot_of(who))
    }

    /// `who`'s next per-agent nonce (== the count of edits that collaborator has
    /// committed — the executor advanced it once per commit).
    pub fn editor_nonce(&self, who: &DreggIdentity) -> u64 {
        self.doc.editor_nonce(self.slot_of(who))
    }

    /// The document's rendered content — clean runs plus any first-class conflict
    /// regions (dregg-doc's own fold).
    pub fn rendered(&self) -> Rendered {
        content(self.doc.graph())
    }

    /// The document's text (conflicts rendered legibly between markers).
    pub fn text(&self) -> String {
        self.rendered().to_marked_string()
    }

    /// The document's live conflict regions (empty in a healthy session — the
    /// landing gate refuses an edit that would introduce one; a conflict can still
    /// be *carried* if one is ever admitted, which is why the surface renders them).
    pub fn conflicts(&self) -> Vec<ConflictRegion> {
        self.rendered().conflicts().cloned().collect()
    }

    /// The document's live cells (atoms) in document order — the editable units.
    pub fn cells(&self) -> Vec<(AtomId, String)> {
        walk_atoms(self.doc.graph())
    }

    /// The single-valued `title` field's live assignments. Two-or-more is a real
    /// [`Regime::Field`] clash.
    pub fn title(&self) -> Vec<String> {
        self.doc
            .graph()
            .field(FIELD_TITLE)
            .iter()
            .map(|a| a.value.clone())
            .collect()
    }

    /// The anchor positions an insert can name: `arg = 0` is the start of the
    /// document (`AtomId::ROOT`); `arg = i` (1-based) is "after the i-th live cell".
    /// Inserting at a NON-tip anchor that another actor has already extended is
    /// exactly the concurrent-edit case that produces an antichain — the landing
    /// gate refuses it.
    pub fn anchors(&self) -> Vec<(i64, String)> {
        let mut out = vec![(0i64, "the start of the document".to_string())];
        for (i, (_, text)) in self.cells().iter().enumerate() {
            out.push(((i + 1) as i64, format!("after \"{text}\"")));
        }
        out
    }

    /// The atom an insert's `arg` anchors after (`0` → `AtomId::ROOT`).
    fn anchor_at(&self, arg: i64) -> Option<AtomId> {
        if arg == 0 {
            return Some(AtomId::ROOT);
        }
        let idx = usize::try_from(arg.checked_sub(1)?).ok()?;
        self.cells().get(idx).map(|(id, _)| *id)
    }

    /// The live atom a delete's `arg` names (1-based over [`DocSession::cells`]).
    fn cell_at(&self, arg: i64) -> Option<AtomId> {
        let idx = usize::try_from(arg.checked_sub(1)?).ok()?;
        self.cells().get(idx).map(|(id, _)| *id)
    }

    /// The number of real verified turns so far (one per landed edit).
    pub fn turns(&self) -> usize {
        self.edits.len()
    }

    /// The document's CURRENT commitment — the shared region cell's real canonical
    /// state commitment, **as the executor wrote it** (the value a light client
    /// trusts). An untouched document's commitment is its genesis cell's.
    pub fn commitment(&self) -> [u8; 32] {
        self.doc.state_commitment()
    }

    /// The public, transmissible session record (the [`RecordVerify`] input).
    pub fn record(&self) -> DocRecord {
        DocRecord {
            edits: self.edits.clone(),
            commitment: self.commitment(),
        }
    }

    /// Per-author contribution counts (dregg-doc's `blame_summary` over the live
    /// fold — attribution that does NOT move when the surrounding text does,
    /// because atom ids are content-addressed).
    pub fn contributions(&self) -> BTreeMap<u64, usize> {
        dregg_doc::blame_summary(self.doc.graph())
            .into_iter()
            .map(|(a, n)| (a.0, n))
            .collect()
    }

    /// Which collaborator an [`Author`] label belongs to (the author id IS the
    /// editor-cell seed).
    pub fn author_name(&self, author: Author) -> String {
        self.roster
            .iter()
            .find(|c| c.seed as u64 == author.0)
            .map(|c| c.who.as_str().to_string())
            .unwrap_or_else(|| format!("author {}", author.0))
    }
}

/// **What the session does with an edit that would leave a conflict standing** —
/// and the reason the [`Regime`] classifier is load-bearing here rather than
/// decorative.
///
/// dregg-doc's two-regime split says a conflict is not one thing: a **prose
/// antichain** (two concurrent inserts at one position) is *illusory* — benign,
/// legible, unilaterally resolvable, never blocking the rest of the document —
/// while a **single-valued field clash** is a *real* conservation/authority clash
/// that [`Regime::needs_consensus`] says must be settled. A collaborative document
/// offering can take either stance, and it should say which:
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConflictPolicy {
    /// **The forge's landing rule** (the default): a shared document stays clean —
    /// an edit that would leave ANY unresolved conflict standing is refused, and
    /// nothing commits. This is `PullRequest::merge`'s
    /// `UnresolvedConflict` discipline restated for a live linear session: the
    /// concurrent author re-anchors at the tip (or opens a branch).
    RefuseUnresolved,
    /// **Conflicts as first-class objects** (dregg-doc's own doctrine): a benign
    /// [`Regime::Prose`] antichain is ADMITTED — it commits as real state, the
    /// surface renders both alternatives with who wrote which, and a later patch
    /// ([`TURN_ORDER_CONFLICT`]) resolves it. A [`Regime::Field`] clash
    /// ([`Regime::needs_consensus`]) is still refused — it is the conservation
    /// boundary. The document never *fails to merge*; it carries the state.
    CarryProseConflicts,
}

/// **The collaborative-document offering.** A stateless factory: each
/// [`open`](Offering::open) is a fresh empty document under a deterministic region
/// identity. `edit_credits` prices a per-edit run-credit (the free tier by default);
/// [`ConflictPolicy`] decides what happens to a conflicting edit.
pub struct DocOffering {
    /// Run-credits a landed edit costs (`0` → free tier). A resolution is always
    /// free — settling a conflict is never taxed.
    edit_credits: u64,
    /// What a conflicting edit does (see [`ConflictPolicy`]).
    policy: ConflictPolicy,
}

impl DocOffering {
    /// The free-tier document (no credit debited per edit), keeping the shared
    /// document clean ([`ConflictPolicy::RefuseUnresolved`]).
    pub fn new() -> Self {
        DocOffering {
            edit_credits: 0,
            policy: ConflictPolicy::RefuseUnresolved,
        }
    }

    /// A paid-tier document: each landed edit costs `credits` run-credits (the
    /// frontend debits them; the core only names the cost). The substrate turn
    /// itself is always free and verifiable.
    pub fn paid(credits: u64) -> Self {
        DocOffering {
            edit_credits: credits,
            policy: ConflictPolicy::RefuseUnresolved,
        }
    }

    /// The document that carries a benign prose antichain as first-class state
    /// (and still refuses a field/authority clash) —
    /// [`ConflictPolicy::CarryProseConflicts`].
    pub fn carrying_prose_conflicts(mut self) -> Self {
        self.policy = ConflictPolicy::CarryProseConflicts;
        self
    }

    /// This offering's conflict policy.
    pub fn policy(&self) -> ConflictPolicy {
        self.policy
    }

    /// The affordances on the document's surface, **cap-gated for `actor`** when one
    /// is given: an actor without the region's edit cap sees every edit affordance
    /// **dimmed** (`enabled: false`) — the cap tooth SHOWN, not hidden. It is only a
    /// decoration: firing a dimmed affordance still lands a real executor
    /// [`Outcome::Refused`] (the executor is the sole referee). With `actor = None`
    /// the affordances are the session's own (enabled where the position is legal).
    ///
    /// The text-bearing affordances (insert / set-title / resolve-title) are
    /// **templates**: their `label` is the human prompt, and the collaborator's prose
    /// is attached to [`Action::text`] by the frontend on actuation (present ->
    /// collect). Index-only affordances (delete / order-conflict) carry no text.
    pub fn actions_for(&self, session: &DocSession, actor: Option<&DreggIdentity>) -> Vec<Action> {
        let may_edit = match actor {
            Some(a) => session
                .role_of(a)
                .map(Role::holds_edit_cap)
                .unwrap_or(false),
            None => true,
        };

        let mut out = Vec::new();
        let cells = session.cells();

        // Append at the tip — the always-clean insert position. A text-TEMPLATE: presented with
        // no content (`text: None`), it SOLICITS the collaborator's prose (`taking_text`), so a
        // frontend routes free text into it as the insert's `Action::text` payload.
        out.push(
            Action::new(
                "…continue the document".to_string(),
                TURN_INSERT,
                cells.len() as i64,
                may_edit,
            )
            .taking_text(),
        );
        // Insert at the start.
        out.push(
            Action::new("…open the document".to_string(), TURN_INSERT, 0, may_edit).taking_text(),
        );
        // Delete each live cell.
        for (i, (_, text)) in cells.iter().enumerate() {
            out.push(Action::new(
                format!("delete \"{text}\""),
                TURN_DELETE,
                (i + 1) as i64,
                may_edit,
            ));
        }
        // The single-valued title (the non-monotone fragment). Also a text template.
        out.push(
            Action::new("set the title".to_string(), TURN_SET_TITLE, 0, may_edit).taking_text(),
        );
        // Resolution affordances — offered only where a conflict actually stands
        // (nothing is fabricated).
        for (i, region) in session.conflicts().iter().enumerate() {
            match region.regime {
                Regime::Field => out.push(
                    Action::new(
                        "settle the title clash".to_string(),
                        TURN_RESOLVE_TITLE,
                        0,
                        may_edit,
                    )
                    .taking_text(),
                ),
                Regime::Prose => out.push(Action::new(
                    "order the concurrent alternatives".to_string(),
                    TURN_ORDER_CONFLICT,
                    i as i64,
                    may_edit,
                )),
            }
        }
        out
    }

    /// The document's surface, **rendered for `actor`** (their cap-gated
    /// affordances). [`Offering::render`] is this with `actor = None`.
    pub fn render_for(&self, session: &DocSession, actor: Option<&DreggIdentity>) -> Surface {
        let rendered = session.rendered();
        let title = match session.title().as_slice() {
            [] => "untitled".to_string(),
            [one] => one.clone(),
            many => format!("CLASH: {}", many.join(" | ")),
        };

        let cells: Vec<ViewNode> = session
            .cells()
            .iter()
            .enumerate()
            .map(|(i, (id, text))| {
                let who = session
                    .doc
                    .graph()
                    .atom(*id)
                    .map(|a| session.author_name(a.provenance.author))
                    .unwrap_or_else(|| "?".to_string());
                ViewNode::Text(format!("[{}] {text}  — {who}", i + 1))
            })
            .collect();

        let roster: Vec<ViewNode> = session
            .roster()
            .iter()
            .map(|c| ViewNode::Text(format!("{} — {}", c.who.as_str(), c.role.label())))
            .collect();

        // THE DIRECTIVE, first — the one sentence saying what to do NOW. The `Text` plaque below
        // is `accent`, so the shared web skin would have promoted ITS first paragraph as the
        // page's lead; on an EMPTY document that paragraph is the empty string and the renderer
        // drops it, so the page opened saying nothing at all about what to do.
        let may_edit = match actor {
            Some(a) => session
                .role_of(a)
                .map(Role::holds_edit_cap)
                .unwrap_or(false),
            None => true,
        };
        let cell_count = session.cells().len();
        let directive = if !may_edit {
            "You are reading this document, not writing it — no edit cap has been granted to your \
             identity, so every control below is inert and a crafted edit would be refused by the \
             executor. Ask a collaborator to invite you."
                .to_string()
        } else if cell_count == 0 {
            "This document is empty — open it by typing a first line into the insert affordance. \
             Every edit lands as a real committed turn carrying its author, so the text below is \
             always attributable and always replayable."
                .to_string()
        } else {
            format!(
                "Continue the document at the tip, or edit one of the {cell_count} cell(s) below. \
                 An insert at an anchor another collaborator has already extended is REFUSED by \
                 the landing gate rather than silently forked, so the text you read is the text \
                 that committed."
            )
        };
        let mut children = vec![
            ViewNode::Section {
                title: "What to do now".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Text(directive)],
            },
            ViewNode::Section {
                title: "Text".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Text(rendered.to_marked_string())],
            },
            ViewNode::Section {
                title: "Cells".to_string(),
                tag: "muted".to_string(),
                children: if cells.is_empty() {
                    vec![ViewNode::Text("(empty document)".to_string())]
                } else {
                    cells
                },
            },
            ViewNode::Section {
                title: "Collaborators".to_string(),
                tag: "muted".to_string(),
                children: if roster.is_empty() {
                    vec![ViewNode::Text("(nobody invited yet)".to_string())]
                } else {
                    roster
                },
            },
            ViewNode::Section {
                title: "Verified edits".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(format!(
                    "{} real committed turns · commitment {}",
                    session.turns(),
                    hex8(&session.commitment())
                ))],
            },
        ];

        // A conflict is a FIRST-CLASS STATE, so the surface shows it (with who wrote
        // which alternative — provenance is a fact, not a guess).
        let conflicts = session.conflicts();
        if !conflicts.is_empty() {
            let mut kids = Vec::new();
            for region in &conflicts {
                let alts: Vec<String> = region
                    .alternatives
                    .iter()
                    .map(|a| {
                        format!(
                            "\"{}\" ({})",
                            a.text,
                            session.author_name(a.provenance.author)
                        )
                    })
                    .collect();
                kids.push(ViewNode::Text(format!(
                    "[{}] {}",
                    region.regime.label(),
                    alts.join("  vs  ")
                )));
            }
            children.push(ViewNode::Section {
                title: "Unresolved".to_string(),
                tag: "warn".to_string(),
                children: kids,
            });
        }

        let items = self
            .actions_for(session, actor)
            .iter()
            .map(|a| MenuItem {
                label: a.label.clone(),
                turn: a.turn.clone(),
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        children.push(ViewNode::Section {
            title: "Edit".to_string(),
            tag: "accent".to_string(),
            children: vec![ViewNode::Menu { items }],
        });

        Surface(ViewNode::Section {
            title: format!("{title} — a shared document"),
            tag: "accent".to_string(),
            children,
        })
    }
}

impl Default for DocOffering {
    fn default() -> Self {
        DocOffering::new()
    }
}

/// Build the real `dregg_doc::Patch` an [`Action`] denotes, at the session's current
/// fold, authored by the actor's editor cell. `None` for an ill-formed affordance
/// (an unknown verb, an out-of-range anchor, a missing/empty text payload) — which
/// is refused without ever reaching the executor (no turn, nothing committed).
///
/// The atom seed is derived from the edit's INDEX in the chain plus the author's
/// cell seed, so it is deterministic under replay (the verifier re-derives the same
/// atom ids — hence the same patch, the same effects, the same `turn_hash`) while
/// still keeping two actors' identical text distinct. A text-bearing edit's prose
/// is read from [`Action::text`] (the first-class payload), never the label.
fn build_patch(session: &DocSession, input: &Action, seed: u8) -> Option<Patch> {
    let author = Author(seed as u64);
    let atom_seed = (session.edits.len() as u64)
        .wrapping_mul(257)
        .wrapping_add(seed as u64)
        .wrapping_add(1);

    // The free-text payload (insert prose, title value) rides `Action::text`.
    let text = input.text.as_deref().unwrap_or("");

    match input.turn.as_str() {
        TURN_INSERT => {
            if text.trim().is_empty() {
                return None;
            }
            let anchor = session.anchor_at(input.arg)?;
            Some(Patch::by(author, [Patch::add(atom_seed, text, anchor).1]))
        }
        TURN_DELETE => {
            let id = session.cell_at(input.arg)?;
            Some(Patch::by(author, [Op::Delete { id }]))
        }
        TURN_SET_TITLE => {
            if text.trim().is_empty() {
                return None;
            }
            Some(Patch::by(
                author,
                [Op::SetField {
                    name: FIELD_TITLE.to_string(),
                    value: text.to_string(),
                    superseding: false,
                }],
            ))
        }
        TURN_RESOLVE_TITLE => {
            if text.trim().is_empty() {
                return None;
            }
            Some(Patch::by(
                author,
                [Op::SetField {
                    name: FIELD_TITLE.to_string(),
                    value: text.to_string(),
                    // SUPERSEDING: collapses the whole clashing assignment set to
                    // this value (dregg-doc's `supersede_field`) — the resolution.
                    superseding: true,
                }],
            ))
        }
        TURN_ORDER_CONFLICT => {
            let idx = usize::try_from(input.arg).ok()?;
            let region = session.conflicts().into_iter().nth(idx)?;
            if region.regime != Regime::Prose {
                return None;
            }
            let heads = region.heads();
            // Order the antichain into a chain: h0 -> h1 -> … (dregg-doc's
            // `Op::Connect` — the prose-conflict resolution primitive).
            let ops: Vec<Op> = heads
                .windows(2)
                .map(|w| Op::Connect {
                    from: w[0],
                    to: w[1],
                })
                .collect();
            if ops.is_empty() {
                return None;
            }
            Some(Patch::by(author, ops))
        }
        _ => None,
    }
}

/// Why an edit was refused, as a human line for the surface.
#[derive(Debug, Clone)]
struct Refusal(String);

/// The landing result of one driven edit.
struct Landed {
    receipt: TurnReceipt,
    doc_commitment: [u8; 32],
}

/// **Drive ONE edit** by editor slot `slot` on the shared [`MultiEditorDoc`], through
/// two gates in dregg-doc's own order:
///
/// 1. **Document soundness** — the fold of the new history must not leave an
///    unresolved conflict standing, as `policy` reads it. The DETECTION is entirely
///    dregg-doc's ([`content`]'s first-class antichain / field-clash regions + the
///    two-regime [`Regime`] classifier); the POLICY is the forge's landing rule.
///    A refused edit is refused BEFORE any turn is built: the executor never sees an
///    unsound document, and the shared `doc` is never touched.
/// 2. **Authority** — the edit is driven through [`MultiEditorDoc::edit`] as the
///    given editor slot's agent, carrying THAT collaborator's nonce + receipt-chain
///    head. An editor without the region's c-list capability is refused IN-BAND by
///    `check_cross_cell_permission` (`TurnError::CapabilityNotHeld`); the executor
///    rolls the ledger back and nothing commits.
///
/// A refusal is total: on any refusal the shared `doc` is byte-identical (gate 1
/// returns before touching it; gate 2's refusal rolls the executor's ledger back and
/// leaves the witness graph un-advanced), and no collaborator's chain moved.
fn drive_on(
    doc: &mut MultiEditorDoc,
    slot: usize,
    patch: &Patch,
    policy: ConflictPolicy,
) -> Result<Landed, Refusal> {
    // GATE 1 — DOCUMENT SOUNDNESS (dregg-doc's own conflict semantics), evaluated
    // on the current shared fold BEFORE any turn is driven.
    let next = patch.apply_to(doc.graph());
    let before = content(doc.graph());
    let after = content(&next);
    // The conflict region this edit would INTRODUCE (one that does not already
    // stand). A resolution introduces none — it removes one.
    let introduced = after
        .conflicts()
        .find(|c| !before.conflicts().any(|b| b == *c))
        .cloned();
    if let Some(region) = introduced {
        let refuse = match policy {
            ConflictPolicy::RefuseUnresolved => true,
            // The two-regime classifier decides: a benign prose antichain is
            // carried as first-class state; a conservation/authority clash is not.
            ConflictPolicy::CarryProseConflicts => region.regime.needs_consensus(),
        };
        if refuse {
            return Err(Refusal(conflict_reason(Some(&region))));
        }
    }

    // GATE 2 — AUTHORITY: the REAL executor (the cap gate lives inside), driving the
    // editing collaborator's own per-agent turn on the shared ledger.
    match doc.edit(slot, patch.clone()) {
        Ok(receipt) => {
            if !doc.commitment_matches_projection() {
                return Err(Refusal(
                    "refused: the committed cell and the document fold diverged".to_string(),
                ));
            }
            Ok(Landed {
                receipt,
                doc_commitment: doc.state_commitment(),
            })
        }
        Err(TurnError::CapabilityNotHeld { .. }) => Err(Refusal(
            "refused by the executor: this actor does not hold the document region's edit \
             capability (TurnError::CapabilityNotHeld) — nothing committed"
                .to_string(),
        )),
        Err(TurnError::EmptyForest) => Err(Refusal(
            "refused: this edit is a no-op at the committed document (nothing to commit)"
                .to_string(),
        )),
        Err(e) => Err(Refusal(format!("refused by the executor: {e:?}"))),
    }
}

/// The refusal line for an edit that would leave the document carrying an
/// unresolved conflict — naming the REGIME (dregg-doc's two-regime classifier:
/// a prose antichain vs a single-valued field/authority clash).
fn conflict_reason(region: Option<&ConflictRegion>) -> String {
    match region {
        Some(c) if c.regime == Regime::Field => format!(
            "refused: this edit leaves an unresolved FIELD conflict on \"{}\" ({} clashing values) \
             — a conservation/authority clash the two-regime classifier says needs consensus; \
             settle it with a superseding resolution",
            c.field.as_deref().unwrap_or(FIELD_TITLE),
            c.alternatives.len()
        ),
        Some(c) => format!(
            "refused: this edit leaves an unresolved PROSE conflict — {} live, mutually-unordered \
             alternatives at one position (a concurrent edit at a stale anchor); re-anchor at the \
             tip, or order the antichain",
            c.alternatives.len()
        ),
        None => "refused: this edit leaves an unresolved conflict".to_string(),
    }
}

impl Offering for DocOffering {
    type Session = DocSession;

    /// Open a fresh shared document: an empty patch history under a deterministic
    /// region identity (the config seed pins the region cell, so a verifier
    /// re-derives the same document cell and a forged record cannot re-target
    /// another one). The shared [`MultiEditorDoc`] starts with just the outsider
    /// slot; collaborators are invited with [`DocSession::invite`].
    fn open(&self, cfg: SessionConfig) -> Result<DocSession, OfferingError> {
        let region_seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        let mut session = DocSession {
            region_seed,
            roster: Vec::new(),
            policy: self.policy,
            // Placeholder — `rebuild` installs the real (signed) doc for the roster.
            doc: MultiEditorDoc::new(region_seed, &[(OUTSIDER_SEED, false)]),
            history: History::new(),
            edits: Vec::new(),
        };
        session.rebuild();
        Ok(session)
    }

    /// The document's edit affordances (session-level; [`DocOffering::actions_for`]
    /// is the per-actor cap-gated view).
    fn actions(&self, session: &DocSession) -> Vec<Action> {
        self.actions_for(session, None)
    }

    /// **The per-VIEWER edit affordances** — the [`Offering::actions_for`] override
    /// that carries the document's per-actor cap dimming ONTO the live host path.
    /// Delegates to the inherent [`DocOffering::actions_for`] with `Some(viewer)`, so
    /// a collaborator without a region's edit cap sees that affordance `disabled`
    /// where a capped collaborator sees it enabled. Without this override the trait
    /// default falls back to [`actions`](Offering::actions) (the anonymous, fully-enabled
    /// set), and the cap dimming would never reach a viewer-aware frontend.
    fn actions_for(&self, session: &DocSession, viewer: &DreggIdentity) -> Vec<Action> {
        // Inherent method (takes `Option<&DreggIdentity>`); resolves ahead of this trait method.
        self.actions_for(session, Some(viewer))
    }

    /// **An EDIT is ONE real turn on the actor's per-agent chain.** The typed
    /// [`Action`] is desugared into a real `dregg_doc::Patch` (its prose read from
    /// [`Action::text`]) and driven through the shared [`MultiEditorDoc`] as the
    /// actor's editor slot:
    ///
    /// - a legal, authorized edit lands a genuine finalized [`TurnReceipt`]
    ///   ([`Outcome::Landed`]) on that collaborator's own chain and advances the
    ///   document's history + fold;
    /// - an edit by an actor without the region's edit cap is a real **executor**
    ///   refusal ([`TurnError::CapabilityNotHeld`]) — [`Outcome::Refused`], nothing
    ///   committed;
    /// - an edit that would leave the document carrying an unresolved conflict is
    ///   refused by dregg-doc's own conflict semantics — [`Outcome::Refused`],
    ///   nothing committed.
    ///
    /// The anti-ghost tooth: on ANY refusal the session is byte-untouched (no
    /// patch, no receipt, no commitment move, no chain advance).
    fn advance(&self, session: &mut DocSession, input: Action, actor: DreggIdentity) -> Outcome {
        let seed = session.seed_of(&actor);
        let slot = session.slot_of(&actor);

        let Some(patch) = build_patch(session, &input, seed) else {
            return Outcome::Refused(format!(
                "refused: \"{}\" (arg {}) is not a well-formed edit on this document",
                input.turn, input.arg
            ));
        };

        match drive_on(&mut session.doc, slot, &patch, self.policy) {
            Ok(landed) => {
                let edit = CommittedEdit {
                    actor,
                    patch: patch.clone(),
                    turn_hash: landed.receipt.turn_hash,
                    effects_hash: landed.receipt.effects_hash,
                    pre_state_hash: landed.receipt.pre_state_hash,
                    post_state_hash: landed.receipt.post_state_hash,
                    doc_commitment: landed.doc_commitment,
                };
                session.history.commit(patch);
                session.edits.push(edit);
                Outcome::Landed {
                    receipt: landed.receipt,
                    // A document is never "ended" — it is a living object.
                    ended: false,
                }
            }
            Err(Refusal(why)) => Outcome::Refused(why),
        }
    }

    /// **Re-verify the document's whole edit chain by RE-DRIVING it.** See
    /// [`RecordVerify::verify_record`] — [`Offering::verify`] is that, over the
    /// session's own authentic record.
    fn verify(&self, session: &DocSession) -> VerifyReport {
        self.verify_record(session, &session.record())
    }

    /// The document's surface: title, text (conflicts legible), the live cells with
    /// their authors, the roster, the verified-turn count + the real commitment, and
    /// the edit affordances as a cap-gated [`ViewNode::Menu`].
    fn render(&self, session: &DocSession) -> Surface {
        self.render_for(session, None)
    }

    /// **The per-VIEWER document surface** — the [`Offering::render_for`] override that
    /// carries the per-actor cap-gated menu ONTO the live host path. Delegates to the
    /// inherent [`DocOffering::render_for`] with `Some(viewer)`, so the surface's edit
    /// affordances are dimmed for a viewer without the edit cap. Without this override
    /// the trait default falls back to [`render`](Offering::render) (the anonymous view).
    fn render_for(&self, session: &DocSession, viewer: &DreggIdentity) -> Surface {
        // Inherent method (takes `Option<&DreggIdentity>`); resolves ahead of this trait method.
        self.render_for(session, Some(viewer))
    }

    /// A landed edit costs `edit_credits` run-credits; a **resolution is free**
    /// (settling a conflict is never taxed). The substrate turn itself is always
    /// free and verifiable — the credit prices the hosted document service.
    fn price(&self, input: &Action) -> RunCost {
        match input.turn.as_str() {
            TURN_RESOLVE_TITLE | TURN_ORDER_CONFLICT => RunCost::free(),
            _ => RunCost::credits(self.edit_credits),
        }
    }
}

/// **The frontend-facing tamper-verify seam.** A frontend holds a [`DocRecord`]
/// (the edit chain) which it may serialize, transmit, and receive back FORGED. It
/// cannot reach the session's authentic identity — the private region seed and the
/// roster (who actually holds the edit cap) — so it cannot re-check the record
/// itself. This seam does: the record supplies only the EDITS; the authentic
/// identity comes from the `session`.
impl RecordVerify for DocOffering {
    type Session = DocSession;
    type Record = DocRecord;

    /// Export the session's authentic record — the edit chain + the final
    /// commitment. No private world identity leaves the offering.
    fn export_record(&self, session: &DocSession) -> DocRecord {
        session.record()
    }

    /// **Re-drive the recorded chain from genesis through the REAL executor.**
    ///
    /// Starting from an empty document under the session's authentic region seed and
    /// its editor roster (a fresh [`MultiEditorDoc`]), each recorded edit is
    /// re-driven as its recorded actor's editor slot (the roster — NOT the record —
    /// decides whether that actor's cell holds the edit cap, so a forger cannot
    /// promote themselves), through the SAME two gates a live edit passes. The
    /// re-drive must reproduce, at every step:
    ///
    /// - that the edit still LANDS (a recorded edit that no longer lands — an
    ///   unauthorized actor, a conflicting patch, a spliced/reordered edit — breaks);
    /// - the turn's deterministic core: `turn_hash` (which binds the editor's prior
    ///   receipt hash) and `effects_hash`;
    /// - the DOCUMENT's commitment after the edit (the real region-cell state
    ///   commitment) — the full ledger state roots are recorded provenance but NOT
    ///   re-compared (see the note at the comparison site: a refused turn consumes
    ///   its nonce on the shared ledger, so the full root is node-level, not a
    ///   function of the committed document chain);
    ///
    /// and finally the whole document must reproduce (the fold of the re-driven
    /// history equals the record's final commitment). The document reproduces from
    /// its edits, or the report is broken.
    fn verify_record(&self, session: &DocSession, record: &DocRecord) -> VerifyReport {
        let n = record.edits.len();
        let mut doc = session.fresh_doc();
        // The commitment the chain stands at: genesis (the fresh region cell), then
        // each edit's own executor-WRITTEN commitment as it is re-driven.
        let mut commitment = doc.state_commitment();

        for (i, edit) in record.edits.iter().enumerate() {
            // The AUTHENTIC identity: the session's roster decides the slot + cap.
            let seed = session.seed_of(&edit.actor);
            let slot = session.slot_of(&edit.actor);
            // The patch's author must be the actor's own editor cell — a patch
            // attributed to someone else's cell is a forged provenance.
            if edit.patch.author != Author(seed as u64) {
                return VerifyReport::broken(
                    i,
                    format!(
                        "edit #{i}: the recorded patch is authored by cell {} but the actor's cell \
                         is {seed} — forged provenance",
                        edit.patch.author.0
                    ),
                );
            }
            match drive_on(&mut doc, slot, &edit.patch, self.policy) {
                Ok(landed) => {
                    if landed.receipt.turn_hash != edit.turn_hash {
                        return VerifyReport::broken(
                            i,
                            format!("edit #{i}: the re-driven turn hash does not match the record"),
                        );
                    }
                    if landed.receipt.effects_hash != edit.effects_hash {
                        return VerifyReport::broken(
                            i,
                            format!("edit #{i}: the re-driven effects hash does not match"),
                        );
                    }
                    // NOTE: the full LEDGER state roots (`pre/post_state_hash`) are
                    // deliberately NOT re-compared. In the shared-ledger multi-editor
                    // model a *refused* turn still consumes the failing agent's nonce
                    // (execute.rs "PHASE 1: Commit fee + nonce — NEVER rolled back"),
                    // so the full ledger root legitimately absorbs concurrent refused
                    // attempts that are not part of the committed document record —
                    // it is a node-level quantity, not reproducible from the document
                    // chain alone. The document-meaningful chain is bound instead by
                    // `turn_hash` (which chains the editor's prior receipt), the
                    // `effects_hash`, and the region `doc_commitment` below — each a
                    // function of the committed chain alone. (An honest boundary,
                    // analogous to why `receipt_hash` is not the recorded chain.)
                    if landed.doc_commitment != edit.doc_commitment {
                        return VerifyReport::broken(
                            i,
                            format!(
                                "edit #{i}: the re-driven document commitment does not match the \
                                 record"
                            ),
                        );
                    }
                    commitment = landed.doc_commitment;
                }
                Err(Refusal(why)) => {
                    return VerifyReport::broken(i, format!("edit #{i} does not re-drive: {why}"));
                }
            }
        }

        if commitment != record.commitment {
            let text: String = content(doc.graph())
                .to_marked_string()
                .chars()
                .take(60)
                .collect();
            return VerifyReport::broken(
                n,
                format!(
                    "the document the recorded edits re-drive (\"{text}\") does not reproduce the \
                     recorded commitment"
                ),
            );
        }
        VerifyReport::ok(n)
    }
}

/// A short hex handle for a 32-byte root (the surface's commitment line).
fn hex8(h: &[u8; 32]) -> String {
    h.iter().take(4).map(|b| format!("{b:02x}")).collect()
}
