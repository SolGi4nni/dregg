//! **The membrane on umems** — distributed branch-and-stitch recast as universal-memory
//! operations.
//!
//! The membrane carries / forks / stitches world-state across instances. The three
//! membrane moves of [`crate::shared_fork`] / [`crate::distributed_card`] —
//!
//! * a **fork** = a confined sub-world the recipient drives;
//! * a **carry** = a serializable snapshot that crosses an instance boundary;
//! * a **stitch** = a pushout-correct, explicitly-lossy merge back.
//!
//! — are re-expressed here over the ONE universal address space of
//! [`dregg_turn::umem`] (the executor-state bridge: every cell field and side-table
//! entry projected to a `(domain, collection, key) ↦ value` cell, the Rust twin of
//! `metatheory/Dregg2/Exec/UniversalBridge.lean`). So:
//!
//! * a **fork** is a **umem branch**: a cap-bounded subgraph projected to a
//!   [`UProjection`] (`UKey ↦ UVal`) — the branch's live state AS a universal map.
//! * a **carry** is a **passable umem**: the [`UProjection`] serializes into a
//!   [`UmemEnvelope`] with an anti-substitution [`UmemEnvelope::umem_root`] tooth
//!   (mirroring [`crate::shared_fork::MembraneFrustum::frustum_root`] and
//!   [`crate::distributed_card::CardForkEnvelope::fork_root`]).
//! * a **stitch** is a **umem merge**: a per-[`UKey`] (per-address) join of two driven
//!   projections against the shared baseline — conflicts surface as first-class
//!   [`UmemConflict`] objects keyed at the EXACT address that diverged (not an opaque
//!   `Atom::Alive` key — the umem recast's whole point: the diff is structured).
//!
//! ## Why this is the revolution
//!
//! [`crate::shared_fork::MembraneFrustum::driven_graphs`] already converts a driven
//! fork's cell-state diff into the [`crate::branch_stitch`] `DocGraph`/`Atom` layer —
//! but it collapses each changed cell to a single opaque `Atom::Alive` at a key derived
//! from `(id ‖ post-state)`. The merge can then only say "this cell changed"; it cannot
//! say *which field*, nor merge two principals' DISJOINT field edits to the SAME cell
//! cleanly. Recasting the payload as a umem lifts the diff to per-address granularity:
//! two principals who touch different `UKey`s of the same cell fold CLEAN; two who touch
//! the SAME `UKey` to different values surface a per-address [`UmemConflict`] (both
//! attributed readings live — never a silent last-writer-wins). Distributed
//! state-handoff becomes **witnessed-umem-handoff**.
//!
//! ## The witness — and the seam
//!
//! A genuine umem handoff is witnessed by the [`dregg_turn::umem`] agreement square
//! `fold(pre, ops) == post` ([`dregg_turn::umem::fold`]) — the executable shadow of the
//! Lean `*_is_memory_program` keystones. Where this prototype carries a real driven
//! [`World`] fork, [`stitch_umem_forks`] re-projects both sides and the merge IS over
//! genuine projections. The STRUCTURE-prototype path ([`stitch_umem_envelopes`]) folds
//! two carried projections directly: it proves the merge algebra + the conflict-object
//! surfacing, but the per-handoff Blum-trace witness (`emit_trace` over the driven
//! journal, binding the carried `pre`→`post` to the executor's op trace) is **the named
//! seam** — it awaits the membrane carrying the op trace alongside the projection (the
//! `UmemTurnWitness` keystone), so a recipient can re-fold and refuse a projection that
//! no genuine turn trace produces. Until then the carry trusts the post-projection
//! under the anti-substitution root tooth (binding, but not turn-derived).
//!
//! gpui-free + `cargo test`-able under `--features embedded-executor`.

use std::collections::{BTreeMap, BTreeSet};

use dregg_cell::CellId;
use dregg_turn::umem::{UKey, UProjection, UVal, project_cell, project_ledger};
use serde::{Deserialize, Serialize};

use crate::world::World;

/// **The stable per-address event id** — a domain-separated blake3 commitment over
/// a [`UKey`]'s canonical postcard bytes, used to surface a umem merge's clean folds
/// and conflicts as the membrane wire's `[u8; 32]` event/conflict ids
/// ([`deos_matrix::membrane::StitchOutcome`] / `ConflictObject`). Where the
/// cell-granular `Atom` stitch keyed an event at `(cell-id ‖ post-state)` — opaque
/// at the cell — this keys it at the EXACT universal-memory address that moved, so
/// the chat lane's stitch report is field-granular.
pub fn umem_event_id(key: &UKey) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"deos-umem-membrane-event-v1");
    let kb = postcard::to_stdvec(key).expect("UKey is postcard-serializable");
    h.update(&(kb.len() as u64).to_le_bytes());
    h.update(&kb);
    *h.finalize().as_bytes()
}

/// **A cap-bounded subgraph projected to a universal map — the FORK as a umem branch.**
///
/// Mints from a [`World`] by BFS-culling the subgraph in view of a `focus` cell (the
/// guest principal whose c-list reach defines the in-view set, exactly the
/// [`crate::shared_fork::MembraneFrustum`] frustum cull), then PROJECTING each culled
/// cell into the universal address space ([`dregg_turn::umem::project_ledger`] restricted
/// to the culled cells). The result is the branch's live state AS a `UKey ↦ UVal` map —
/// the umem branch the recipient drives + stitches.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UmemBranch {
    /// The focus cell the cull is centered on (the guest principal whose reach bounds it).
    pub focus: CellId,
    /// Max hops along capability edges from the focus (the far plane).
    pub max_depth: u8,
    /// The cells in view, in cell-id order (the cull, recorded so the projection re-derives).
    pub cells: Vec<CellId>,
    /// The universal-memory projection of EXACTLY the culled subgraph — the umem branch.
    pub umem: UProjection,
    /// The witness cursor (height) the branch was minted at.
    pub minted_height: u64,
}

impl UmemBranch {
    /// **Mint a umem branch from a world.** BFS over capability edges from `focus` to
    /// `max_depth` (the same cull as the cell-subgraph membrane), then project the culled
    /// cells into the universal address space. The projection is restricted to the culled
    /// cells: a recipient gets the focus's reach and nothing beyond it (anti-amplification
    /// by omission — a `UKey` whose cell was not culled is absent and unreachable).
    pub fn mint(world: &World, focus: CellId, max_depth: u8) -> Self {
        let ledger = world.ledger();
        // (1) The frustum cull: reachable cells from the focus to the depth bound.
        let mut seen: BTreeSet<CellId> = BTreeSet::new();
        let mut frontier: Vec<CellId> = vec![focus];
        seen.insert(focus);
        for _ in 0..=max_depth {
            let mut next: Vec<CellId> = Vec::new();
            for id in frontier.drain(..) {
                if let Some(cell) = ledger.get(&id) {
                    for cap in cell.capabilities.iter() {
                        if seen.insert(cap.target) {
                            next.push(cap.target);
                        }
                    }
                }
            }
            if next.is_empty() {
                break;
            }
            frontier = next;
        }
        // (2) Project the WHOLE ledger, then keep only umem cells whose cell is in view
        //     (or non-cell planes — nullifiers/factories/index — which are global and not
        //     part of the per-principal subgraph cull, so they are dropped here too).
        let full = project_ledger(ledger);
        let umem: UProjection = full
            .into_iter()
            .filter(|(k, _)| matches!(k.cell(), Some(c) if seen.contains(&c)))
            .collect();
        let cells: Vec<CellId> = seen.into_iter().collect();
        UmemBranch {
            focus,
            max_depth,
            cells,
            umem,
            minted_height: world.height(),
        }
    }

    /// **Project a carried [`MembraneFrustum`] into a umem branch — the live
    /// membrane's CARRY recast as a passable umem.** The frustum already carries the
    /// cap-bounded cell subgraph (the cull) the membrane ships; this projects EXACTLY
    /// those cells into the universal address space, so the bytes that cross the
    /// boundary witness a `UProjection` (its [`UmemBranch::umem_root`] the handoff
    /// tooth — derived from the SAME cells the frustum's
    /// [`crate::shared_fork::MembraneFrustum::frustum_root`] binds). This is the bridge
    /// that makes [`crate::shared_fork::ForkMembraneHost`]'s carry a witnessed umem
    /// rather than only an opaque `Cell` blob.
    pub fn from_frustum(frustum: &crate::shared_fork::MembraneFrustum) -> Self {
        let mut umem = UProjection::new();
        for cell in &frustum.cells {
            project_cell(cell, &mut umem);
        }
        let mut cells: Vec<CellId> = frustum.cells.iter().map(|c| c.id()).collect();
        cells.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
        UmemBranch {
            focus: frustum.focus,
            max_depth: frustum.max_depth,
            cells,
            umem,
            minted_height: frustum.minted_height,
        }
    }

    /// **The umem-branch root — the anti-substitution tooth.** A domain-separated
    /// blake3 commitment over EXACTLY the projected `(UKey, UVal)` pairs (in `BTreeMap`
    /// canonical order), so mint and carry MUST agree (else fail-closed at
    /// [`open_umem_envelope`]). Mirrors
    /// [`crate::shared_fork::MembraneFrustum::frustum_root`], but binds the universal-map
    /// projection rather than the raw cell bytes.
    pub fn umem_root(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"deos-umem-membrane-branch-root-v1");
        h.update(self.focus.as_bytes());
        h.update(&[self.max_depth]);
        h.update(&self.minted_height.to_le_bytes());
        h.update(&(self.umem.len() as u64).to_le_bytes());
        // BTreeMap iterates in key order — canonical. Each (key, value) folds via its
        // postcard bytes (deterministic — serde emits in declaration order).
        for (k, v) in self.umem.iter() {
            let kb = postcard::to_stdvec(k).expect("UKey is postcard-serializable");
            let vb = postcard::to_stdvec(v).expect("UVal is postcard-serializable");
            h.update(&(kb.len() as u64).to_le_bytes());
            h.update(&kb);
            h.update(&(vb.len() as u64).to_le_bytes());
            h.update(&vb);
        }
        *h.finalize().as_bytes()
    }
}

/// **A umem branch made portable — the CARRY as a passable umem.**
///
/// The serializable envelope that crosses an instance boundary (the twin of
/// [`crate::shared_fork::MembraneFrustum`] and
/// [`crate::distributed_card::CardForkEnvelope`]), carrying the universal-map projection
/// + the anti-substitution root. The bytes are inert in transit; a recipient opens them
/// (the root tooth fires fail-closed on a substituted payload) and stitches.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UmemEnvelope {
    /// The carried umem branch (focus, cull, the `UProjection`, the cursor).
    pub branch: UmemBranch,
    /// The claimed root the originator commits to (re-checked at open — anti-substitution).
    pub claimed_root: [u8; 32],
}

impl UmemEnvelope {
    /// Seal a minted branch for carry: the wire bytes + the claimed root. The originator
    /// hands both to the membrane; the recipient opens the bytes against the root.
    pub fn seal(branch: UmemBranch) -> (Vec<u8>, [u8; 32]) {
        let claimed_root = branch.umem_root();
        let env = UmemEnvelope {
            branch,
            claimed_root,
        };
        (env.to_bytes(), claimed_root)
    }

    /// Serialize for the wire — postcard, the canonical codec.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("umem envelope is postcard-serializable")
    }

    /// The carried projection's own root (re-derived from the carried branch).
    pub fn umem_root(&self) -> [u8; 32] {
        self.branch.umem_root()
    }
}

/// **Open a received umem envelope, fail-closed.** Deserialize the wire bytes and fire
/// the anti-substitution tooth: the decoded branch MUST reproduce the `expected_root`
/// AND that root must equal the envelope's own `claimed_root` (a tampered projection is
/// refused before a single address is trusted). Mirrors
/// [`crate::distributed_card::open_envelope`].
pub fn open_umem_envelope(
    bytes: &[u8],
    expected_root: [u8; 32],
) -> Result<UmemEnvelope, UmemMembraneError> {
    let env: UmemEnvelope =
        postcard::from_bytes(bytes).map_err(|_| UmemMembraneError::MalformedEnvelope)?;
    if env.umem_root() != expected_root || env.claimed_root != expected_root {
        return Err(UmemMembraneError::RootMismatch);
    }
    Ok(env)
}

/// **A per-address conflict object — the umem recast's first-class conflict.**
///
/// When two driven projections both changed the SAME [`UKey`] to DIFFERENT values
/// (relative to the shared baseline), the merge cannot silently pick one. The conflict is
/// surfaced HERE, at the exact address, carrying BOTH attributed alternatives (the loser
/// is never hidden — the same discipline as the card stitch's `ConflictRegion`). This is
/// the structured replacement for `branch_stitch`'s opaque `Atom::Dead`-wins collapse:
/// the conflict names the field, not just "the cell changed".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UmemConflict {
    /// The exact universal-memory address both sides diverged on.
    pub key: UKey,
    /// The shared-baseline value at this address before either drive (`None` = absent).
    pub base: Option<UVal>,
    /// The "main"/originator side's driven value (`None` = it deleted the address).
    pub a: Option<UVal>,
    /// The branch/recipient side's driven value (`None` = it deleted the address).
    pub b: Option<UVal>,
}

/// **The outcome of a umem merge — the STITCH.** The clean-folded projection plus the
/// per-address conflict objects the merge could not auto-resolve. The clean part is the
/// I-confluent fold (each side's disjoint changes both kept); the conflicts await an
/// explicit resolution (mirroring the cross-party held-promise hole of
/// [`crate::branch_stitch::CrossPartyResolution`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UmemStitch {
    /// The clean-merged projection: the baseline with each side's non-conflicting
    /// changes folded in. At a conflicted address it carries the BASELINE value (the
    /// pre-resolution state — the conflict object holds the alternatives).
    pub merged: UProjection,
    /// The first-class per-address conflicts (empty = a fully clean merge).
    pub conflicts: Vec<UmemConflict>,
}

impl UmemStitch {
    /// A fully clean merge (no conflicts)?
    pub fn is_clean(&self) -> bool {
        self.conflicts.is_empty()
    }

    /// Resolve a conflicted address by choosing one alternative (`a`, `b`, or a fresh
    /// value), folding it into `merged` and dropping the conflict. The explicit,
    /// linear-logic-forced resolution — the value is CHOSEN, never silently merged.
    /// Returns `false` if `key` is not a live conflict.
    pub fn resolve(&mut self, key: &UKey, choice: Option<UVal>) -> bool {
        let Some(pos) = self.conflicts.iter().position(|c| &c.key == key) else {
            return false;
        };
        self.conflicts.remove(pos);
        match choice {
            Some(v) => {
                self.merged.insert(key.clone(), v);
            }
            None => {
                self.merged.remove(key);
            }
        }
        true
    }
}

/// **THE UMEM MERGE — the stitch over two driven projections against a shared baseline.**
///
/// The pushout-shaped, per-address fold. For every address touched by either side:
///
/// * untouched by both → the baseline value (unchanged).
/// * touched by exactly one side (the other left the baseline) → that side's value
///   (a clean, I-confluent fold — the disjoint edit is kept).
/// * touched by BOTH to the SAME value → that agreed value (concurrent agreement, clean).
/// * touched by BOTH to DIFFERENT values → a [`UmemConflict`] object at the address; the
///   `merged` map keeps the baseline value pending an explicit resolution.
///
/// This is the universal-map twin of [`crate::branch_stitch::DocGraph::merge`] — but the
/// join is per-`UKey`, so two principals editing DIFFERENT fields of the SAME cell fold
/// CLEAN (where the cell-granular `Atom` merge would have collided), and a real collision
/// names the exact address.
pub fn stitch_projections(base: &UProjection, a: &UProjection, b: &UProjection) -> UmemStitch {
    let mut keys: BTreeSet<&UKey> = BTreeSet::new();
    keys.extend(base.keys());
    keys.extend(a.keys());
    keys.extend(b.keys());

    let mut merged: UProjection = BTreeMap::new();
    let mut conflicts: Vec<UmemConflict> = Vec::new();

    for k in keys {
        let bv = base.get(k);
        let av = a.get(k);
        let bbv = b.get(k);
        // Did each side change the address relative to the baseline?
        let a_changed = av != bv;
        let b_changed = bbv != bv;
        match (a_changed, b_changed) {
            (false, false) => {
                // Unchanged by both — carry the baseline (if present).
                if let Some(v) = bv {
                    merged.insert(k.clone(), v.clone());
                }
            }
            (true, false) => {
                // Only A changed — keep A's value (clean).
                if let Some(v) = av {
                    merged.insert(k.clone(), v.clone());
                }
            }
            (false, true) => {
                // Only B changed — keep B's value (clean).
                if let Some(v) = bbv {
                    merged.insert(k.clone(), v.clone());
                }
            }
            (true, true) => {
                if av == bbv {
                    // Both changed to the SAME value — concurrent agreement, clean.
                    if let Some(v) = av {
                        merged.insert(k.clone(), v.clone());
                    }
                } else {
                    // Both changed to DIFFERENT values — a first-class per-address
                    // conflict. `merged` keeps the baseline pending explicit resolution.
                    if let Some(v) = bv {
                        merged.insert(k.clone(), v.clone());
                    }
                    conflicts.push(UmemConflict {
                        key: k.clone(),
                        base: bv.cloned(),
                        a: av.cloned(),
                        b: bbv.cloned(),
                    });
                }
            }
        }
    }
    UmemStitch { merged, conflicts }
}

/// **Stitch two carried umem envelopes** by the umem merge — the string-only / projection
/// -only distributed stitch (both sides carry their driven projection over the boundary;
/// the merge happens at a third place, or where the recipient need not hold a live fork).
///
/// Both envelopes MUST carry projections of the SAME focus subgraph; `base` is the shared
/// minted baseline both branched from (the originator's pre-drive projection). The
/// per-address merge folds A's driven projection against B's. This is the
/// STRUCTURE-prototype path — see the module's named seam (the per-handoff Blum-trace
/// witness awaits the envelope carrying the op trace).
pub fn stitch_umem_envelopes(base: &UmemBranch, a: &UmemEnvelope, b: &UmemEnvelope) -> UmemStitch {
    stitch_projections(&base.umem, &a.branch.umem, &b.branch.umem)
}

/// **Stitch a carried umem envelope against a recipient's live driven fork** by the umem
/// merge — the distributed twin of [`crate::distributed_card::stitch_with_fork`].
///
/// `base` is the shared minted baseline; `a` is the carried originator envelope (off the
/// wire); `b_fork` is the recipient's OWN live driven [`World`] fork, re-projected here
/// over the SAME focus + depth as the baseline (so both legs are universal maps of the
/// same subgraph). Re-projecting the live fork means the merge folds the recipient's
/// genuine executor-committed state — this is the executor-real half (the originator's
/// half is trusted under the root tooth; binding both halves to op traces is the seam).
pub fn stitch_umem_forks(base: &UmemBranch, a: &UmemEnvelope, b_fork: &World) -> UmemStitch {
    let b = UmemBranch::mint(b_fork, base.focus, base.max_depth);
    stitch_projections(&base.umem, &a.branch.umem, &b.umem)
}

// ════════════════════════════════════════════════════════════════════════════════════════
// THE SETTLEMENT-SOUND STITCH — Settlement Soundness realized on the LIVE multiplayer.
//
// The umem merge above is pushout-correct over STATE (the field-granular fold). Distributed
// time-travel adds a second, non-monotone axis: AUTHORITY. A branch-and-stitch lets parties
// fork a PAST config into a virtualized world, experiment there, and reconcile back — but a
// capability that was LIVE when the branch was spun up may be REVOKED before the branch is
// finalized. Revocation is the one non-monotone operation, so the stitch MUST evaluate every
// conferred authority at the SETTLEMENT TIP (the live main world after any revocation), NOT at
// branch time. This is the operable face of the two proven Lean keystones:
//
//   * `Metatheory.SettlementSoundness.stitch_drops_revoked_authority` — "a cap I have since
//     revoked cannot ride a stitch into my real world": the linear DROP IS an unsettleable
//     revoked-authority confer.
//   * `Dregg2.Circuit.SettlementSoundness.settlement_soundness` — a verifying finalized batch
//     yields a genuine transition whose authority is HONORED AT THE SETTLEMENT TIP
//     (`honorsAtSettlement`), not at the branch.
//
// The state pushout (`stitch_projections`) and the authority gate (`settle_umem_stitch`) are
// ORTHOGONAL: the disjoint umem edits fold clean / a same-address clash is held fail-closed
// REGARDLESS of authority, and a conferred cap rides into main ONLY if held at the settlement
// tip. A cap revoked between branch and tip is LINEAR-DROPPED — never conferred, never conjured.

/// **A capability a stitch would confer back into main — the live, `CellId`-native twin of
/// [`crate::branch_stitch::BranchCap`].** Named by the live cell it reaches and whether it
/// confers debit (drain/write) reach. The settlement gate checks every conferred cap against
/// the authority the author HELD AT THE SETTLEMENT TIP (read from the live world after any
/// revocation) — authority is evaluated at settlement, not at branch time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConferredCap {
    /// The live cell this cap reaches.
    pub target: CellId,
    /// Whether the cap confers debit (drain/write) reach to `target`. A read-only view sets
    /// this `false`; a write/node cap sets it `true`. Mirrors `BranchCap::debit_reach`.
    pub debit_reach: bool,
}

/// **The settlement-tip held-authority view — `settledRevView` realized on the live ledger.**
///
/// Reads the caps `author` holds in the LIVE world AT THE SETTLEMENT TIP (i.e. AFTER any
/// `RevokeCapability` turn committed between branch and settlement). This is the operable
/// `Dregg2.Circuit.SettlementSoundness.settledRevView` — the authority view a faithful
/// settlement reads at the finalized tip, NOT the (stale) branch-time view a branch was built
/// against. A cap the author has since revoked is structurally absent here, so the gate drops
/// any stitch that tries to confer it.
///
/// Each live cap becomes a `ConferredCap` with `debit_reach = true` whenever the cap is live
/// (`permissions != Impossible`) — a held cap confers reach; only an `Impossible`/absent cap
/// fails the gate.
pub fn settlement_held_at_tip(world: &World, author: CellId) -> Vec<ConferredCap> {
    let Some(cell) = world.ledger().get(&author) else {
        return Vec::new();
    };
    cell.capabilities
        .iter()
        .filter(|c| c.permissions != dregg_cell::AuthRequired::Impossible)
        .map(|c| ConferredCap {
            target: c.target,
            debit_reach: true,
        })
        .collect()
}

/// **A settlement-sound umem stitch — the field-granular pushout PLUS the settlement gate.**
///
/// Carries the pushout merge (`stitch`, with its conflicts held fail-closed) and the verdict
/// of the authority gate: which conferred caps were LIVE at the settlement tip and ride into
/// main (`admitted`), and which were revoked-before-tip and were LINEAR-DROPPED (`dropped`).
/// The DROP is lossy but pushout-correct on authority: a revoked cap is never conferred and
/// never conjured — the merged STATE is unaffected, only the authority confer is dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettledUmemStitch {
    /// The field-granular pushout merge (conflicts held pending explicit resolution).
    pub stitch: UmemStitch,
    /// Conferred caps that were HELD AT THE SETTLEMENT TIP — they ride the stitch into main.
    pub admitted: Vec<ConferredCap>,
    /// Conferred caps NOT held at the settlement tip (revoked between branch and tip) — the
    /// linear DROP. "A cap I have since revoked cannot ride a stitch into my real world."
    pub dropped: Vec<ConferredCap>,
}

impl SettledUmemStitch {
    /// **Does the stitch settle?** Fail-closed: it settles only when the state pushout has NO
    /// live conflicts (every same-address clash explicitly resolved). The linear-dropped caps
    /// do NOT block settlement — they were simply not conferred (authority is read at the tip).
    pub fn settles(&self) -> bool {
        self.stitch.is_clean()
    }

    /// The settled merged-umem root (the anti-substitution commitment over the merged
    /// projection), `Some` iff the stitch settles (no live conflict). Mirrors the membrane
    /// stitch's `settled_root` — a binding root only once the merge is fail-closed clean.
    pub fn settled_root(&self) -> Option<[u8; 32]> {
        if !self.settles() {
            return None;
        }
        let mut h = blake3::Hasher::new();
        h.update(b"deos-umem-membrane-settled-root-v1");
        h.update(&(self.stitch.merged.len() as u64).to_le_bytes());
        for (k, v) in self.stitch.merged.iter() {
            let kb = postcard::to_stdvec(k).expect("UKey is postcard-serializable");
            let vb = postcard::to_stdvec(v).expect("UVal is postcard-serializable");
            h.update(&(kb.len() as u64).to_le_bytes());
            h.update(&kb);
            h.update(&(vb.len() as u64).to_le_bytes());
            h.update(&vb);
        }
        Some(*h.finalize().as_bytes())
    }
}

/// **THE SETTLEMENT-SOUND STITCH — Settlement Soundness on the live multiplayer.**
///
/// Welds the field-granular state pushout (`stitch`) to the authority gate. Every conferred cap
/// is checked against `settlement_held` (the authority read at the SETTLEMENT TIP via
/// [`settlement_held_at_tip`]): a cap whose target is held — with debit reach if the confer
/// claims it — is ADMITTED; a cap revoked-before-tip is LINEAR-DROPPED. The gate predicate is
/// IDENTICAL to the proven control model [`crate::branch_stitch::Stitch::settle`]
/// (`held.target == c.target && (held.debit_reach || !c.debit_reach)`), but lossy-per-cap (a
/// drop) rather than whole-stitch refusal, exactly as the membrane lossy-drops an over-conferred
/// cap while the disjoint merge proceeds.
///
/// Pushout-correct (the state merge is untouched by the gate) AND settlement-sound (no revoked
/// authority rides in). The operable shadow of `stitch_drops_revoked_authority`.
pub fn settle_umem_stitch(
    stitch: UmemStitch,
    conferred: &[ConferredCap],
    settlement_held: &[ConferredCap],
) -> SettledUmemStitch {
    let mut admitted = Vec::new();
    let mut dropped = Vec::new();
    for c in conferred {
        // Held at the settlement tip? (the `branch_stitch::Stitch::settle` gate predicate)
        let held = settlement_held
            .iter()
            .any(|h| h.target == c.target && (h.debit_reach || !c.debit_reach));
        if held {
            admitted.push(c.clone());
        } else {
            // Revoked between branch and tip → the linear DROP (never conferred, never conjured).
            dropped.push(c.clone());
        }
    }
    SettledUmemStitch {
        stitch,
        admitted,
        dropped,
    }
}

/// Errors the umem membrane raises (the fail-closed paths — mirroring
/// [`crate::shared_fork::MembraneError`] / [`crate::distributed_card::DistributedCardError`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UmemMembraneError {
    /// The envelope bytes did not deserialize into a umem envelope (corrupt/truncated) —
    /// fail-closed.
    MalformedEnvelope,
    /// The decoded projection did not reproduce the claimed root — the anti-substitution
    /// tooth fired (refuse before trusting one address).
    RootMismatch,
}

impl std::fmt::Display for UmemMembraneError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UmemMembraneError::MalformedEnvelope => {
                write!(f, "umem envelope is malformed (not a valid envelope)")
            }
            UmemMembraneError::RootMismatch => write!(
                f,
                "umem root mismatch — refusing to open a substituted projection (fail-closed)"
            ),
        }
    }
}

impl std::error::Error for UmemMembraneError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{make_open_cell, set_field};
    use dregg_cell::AuthRequired;

    /// A signed source world: a `room` focus reaching two principals A and B and the
    /// docs they edit — `shared` (both reach it: the conflict candidate), `doc_a` (only
    /// A), `doc_b` (only B). Returns `(world, room, user_a, user_b, shared, doc_a, doc_b)`.
    #[allow(clippy::type_complexity)]
    fn mp_world() -> (World, CellId, CellId, CellId, CellId, CellId, CellId) {
        let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
        let shared = w.genesis_cell(0x5D, 0);
        let doc_a = w.genesis_cell(0xA1, 0);
        let doc_b = w.genesis_cell(0xB2, 0);
        let mut a = make_open_cell(0x0A, 0);
        a.capabilities
            .grant(shared, AuthRequired::None)
            .expect("A holds shared");
        a.capabilities
            .grant(doc_a, AuthRequired::None)
            .expect("A holds doc_a");
        let user_a = w.genesis_install(a);
        let mut b = make_open_cell(0x0B, 0);
        b.capabilities
            .grant(shared, AuthRequired::None)
            .expect("B holds shared");
        b.capabilities
            .grant(doc_b, AuthRequired::None)
            .expect("B holds doc_b");
        let user_b = w.genesis_install(b);
        let mut room = make_open_cell(0x40, 0);
        room.capabilities
            .grant(user_a, AuthRequired::None)
            .expect("room reaches A");
        room.capabilities
            .grant(user_b, AuthRequired::None)
            .expect("room reaches B");
        let room = w.genesis_install(room);
        (w, room, user_a, user_b, shared, doc_a, doc_b)
    }

    /// THE FULL LOOP, clean: fork → carry → stitch as umem operations, two principals
    /// editing DISJOINT addresses fold clean (the per-address win over the cell-granular
    /// `Atom` merge).
    #[test]
    fn fork_carry_stitch_disjoint_edits_fold_clean() {
        let (world, room, _ua, _ub, _shared, doc_a, doc_b) = mp_world();

        // ── BASELINE: mint the shared umem branch (the fork as a umem). ──────────────
        let base = UmemBranch::mint(&world, room, 3);
        assert!(
            !base.umem.is_empty(),
            "the projection captured the in-view subgraph"
        );
        assert!(
            base.umem.contains_key(&UKey::Field {
                cell: doc_a,
                slot: 0,
            }),
            "doc_a's field-0 address is in the umem branch"
        );

        // ── A: drive its OWN fork — edit doc_a's field 0. CARRY it as a umem envelope. ─
        let mut fork_a = world.fork();
        let _ = fork_a.commit_turn(fork_a.turn(_ua, vec![set_field(doc_a, 0, [0xAA; 32])]));
        let branch_a = UmemBranch::mint(&fork_a, room, 3);
        let (a_bytes, a_root) = UmemEnvelope::seal(branch_a);

        // ── B (another instance): drive its fork — edit doc_b's field 0 (a DISJOINT
        //    address). CARRY it too. ───────────────────────────────────────────────────
        let mut fork_b = world.fork();
        let _ = fork_b.commit_turn(fork_b.turn(_ub, vec![set_field(doc_b, 0, [0xBB; 32])]));
        let branch_b = UmemBranch::mint(&fork_b, room, 3);
        let (b_bytes, b_root) = UmemEnvelope::seal(branch_b);

        // ── OPEN both (anti-substitution root tooth admits the genuine projections). ──
        let env_a = open_umem_envelope(&a_bytes, a_root).expect("A's genuine envelope opens");
        let env_b = open_umem_envelope(&b_bytes, b_root).expect("B's genuine envelope opens");

        // ── STITCH: the umem merge folds the two driven projections. ─────────────────
        let stitch = stitch_umem_envelopes(&base, &env_a, &env_b);
        assert!(
            stitch.is_clean(),
            "DISJOINT per-address edits fold CLEAN: conflicts = {:?}",
            stitch.conflicts
        );
        // BOTH principals' edits survive (co-drive, not LWW) — at their exact addresses.
        assert_eq!(
            stitch.merged.get(&UKey::Field {
                cell: doc_a,
                slot: 0,
            }),
            Some(&UVal::Bytes32([0xAA; 32])),
            "A's doc_a edit kept in the merged umem"
        );
        assert_eq!(
            stitch.merged.get(&UKey::Field {
                cell: doc_b,
                slot: 0,
            }),
            Some(&UVal::Bytes32([0xBB; 32])),
            "B's doc_b edit kept in the merged umem"
        );
    }

    /// THE per-address conflict: two principals edit the SAME address to DIFFERENT values
    /// → a first-class `UmemConflict` object (both attributed readings live), resolvable.
    #[test]
    fn same_address_conflict_surfaces_a_resolvable_object() {
        let (world, room, _ua, _ub, shared, _da, _db) = mp_world();
        let base = UmemBranch::mint(&world, room, 3);

        // A and B both edit shared's field 0 — to DIFFERENT values (the collision).
        let mut fork_a = world.fork();
        let _ = fork_a.commit_turn(fork_a.turn(_ua, vec![set_field(shared, 0, [0x11; 32])]));
        let (a_bytes, a_root) = UmemEnvelope::seal(UmemBranch::mint(&fork_a, room, 3));

        let mut fork_b = world.fork();
        let _ = fork_b.commit_turn(fork_b.turn(_ub, vec![set_field(shared, 0, [0x22; 32])]));
        let (b_bytes, b_root) = UmemEnvelope::seal(UmemBranch::mint(&fork_b, room, 3));

        let env_a = open_umem_envelope(&a_bytes, a_root).unwrap();
        let env_b = open_umem_envelope(&b_bytes, b_root).unwrap();

        let mut stitch = stitch_umem_envelopes(&base, &env_a, &env_b);
        assert!(
            !stitch.is_clean(),
            "two edits to the SAME address MUST surface a conflict"
        );
        let key = UKey::Field {
            cell: shared,
            slot: 0,
        };
        let conflict = stitch
            .conflicts
            .iter()
            .find(|c| c.key == key)
            .expect("the conflict names the EXACT address");
        // Both attributed alternatives live — the loser is never hidden.
        assert_eq!(
            conflict.a,
            Some(UVal::Bytes32([0x11; 32])),
            "A's reading lives"
        );
        assert_eq!(
            conflict.b,
            Some(UVal::Bytes32([0x22; 32])),
            "B's reading lives"
        );
        // Pre-resolution the merge keeps the baseline at the conflicted address.
        let baseline_val = base.umem.get(&key).cloned();
        assert_eq!(
            stitch.merged.get(&key).cloned(),
            baseline_val,
            "the conflicted address holds the baseline pending resolution"
        );

        // RESOLVE explicitly — choose B's reading. The conflict drops; the choice folds.
        assert!(stitch.resolve(&key, Some(UVal::Bytes32([0x22; 32]))));
        assert!(stitch.is_clean(), "resolved — no live conflict remains");
        assert_eq!(
            stitch.merged.get(&key),
            Some(&UVal::Bytes32([0x22; 32])),
            "the chosen reading is folded into the merged umem"
        );
    }

    /// THE umem recast's signature win: two principals edit DIFFERENT fields of the SAME
    /// cell. The cell-granular `Atom` merge would collide (one opaque atom per changed
    /// cell); the umem merge folds CLEAN because the addresses differ.
    #[test]
    fn disjoint_fields_of_same_cell_fold_clean_the_umem_win() {
        let (world, room, _ua, _ub, shared, _da, _db) = mp_world();
        let base = UmemBranch::mint(&world, room, 3);

        // A edits shared.field[0]; B edits shared.field[1] — SAME cell, DIFFERENT address.
        let mut fork_a = world.fork();
        let _ = fork_a.commit_turn(fork_a.turn(_ua, vec![set_field(shared, 0, [0x11; 32])]));
        let (a_bytes, a_root) = UmemEnvelope::seal(UmemBranch::mint(&fork_a, room, 3));

        let mut fork_b = world.fork();
        let _ = fork_b.commit_turn(fork_b.turn(_ub, vec![set_field(shared, 1, [0x22; 32])]));
        let (b_bytes, b_root) = UmemEnvelope::seal(UmemBranch::mint(&fork_b, room, 3));

        let env_a = open_umem_envelope(&a_bytes, a_root).unwrap();
        let env_b = open_umem_envelope(&b_bytes, b_root).unwrap();
        let stitch = stitch_umem_envelopes(&base, &env_a, &env_b);

        assert!(
            stitch.is_clean(),
            "DISJOINT fields of the SAME cell fold CLEAN (the umem-granularity win): {:?}",
            stitch.conflicts
        );
        assert_eq!(
            stitch.merged.get(&UKey::Field {
                cell: shared,
                slot: 0,
            }),
            Some(&UVal::Bytes32([0x11; 32])),
            "A's field-0 edit kept"
        );
        assert_eq!(
            stitch.merged.get(&UKey::Field {
                cell: shared,
                slot: 1,
            }),
            Some(&UVal::Bytes32([0x22; 32])),
            "B's field-1 edit kept — both fields of one cell merged"
        );
    }

    /// The live-fork stitch ([`stitch_umem_forks`]) and the envelope stitch
    /// ([`stitch_umem_envelopes`]) AGREE — both are the SAME umem merge (the executor-real
    /// half re-projects the recipient's genuine driven fork).
    #[test]
    fn live_fork_stitch_matches_envelope_stitch() {
        let (world, room, _ua, _ub, doc_a, _shared, doc_b) = mp_world();
        let base = UmemBranch::mint(&world, room, 3);

        let mut fork_a = world.fork();
        let _ = fork_a.commit_turn(fork_a.turn(_ua, vec![set_field(doc_a, 0, [0xAA; 32])]));
        let (a_bytes, a_root) = UmemEnvelope::seal(UmemBranch::mint(&fork_a, room, 3));
        let env_a = open_umem_envelope(&a_bytes, a_root).unwrap();

        let mut fork_b = world.fork();
        let _ = fork_b.commit_turn(fork_b.turn(_ub, vec![set_field(doc_b, 0, [0xBB; 32])]));
        let (b_bytes, b_root) = UmemEnvelope::seal(UmemBranch::mint(&fork_b, room, 3));
        let env_b = open_umem_envelope(&b_bytes, b_root).unwrap();

        let via_envelopes = stitch_umem_envelopes(&base, &env_a, &env_b);
        let via_fork = stitch_umem_forks(&base, &env_a, &fork_b);
        assert_eq!(
            via_envelopes, via_fork,
            "the live-fork stitch and the envelope stitch are the SAME umem merge"
        );
    }

    // ── SETTLEMENT-SOUND STITCH — the authority gate (both polarities) ──────────────────

    /// The settlement gate ADMITS a cap held at the tip and DROPS one revoked-before-tip — the
    /// linear DROP. The state pushout is untouched (orthogonal): authority is read at settlement.
    #[test]
    fn settle_drops_revoked_authority_admits_held() {
        let (world, room, ua, _ub, _shared, doc_a, not_held) = mp_world();
        // Here we model the settlement-tip held set directly to exercise the gate in isolation
        // (the live, revocation-driven held view is covered by the integration test and by
        // `settlement_held_at_tip_reflects_a_real_revocation`).
        let base = UmemBranch::mint(&world, room, 3);
        let mut fork_a = world.fork();
        let _ = fork_a.commit_turn(fork_a.turn(ua, vec![set_field(doc_a, 0, [0xAA; 32])]));
        let (a_bytes, a_root) = UmemEnvelope::seal(UmemBranch::mint(&fork_a, room, 3));
        let env_a = open_umem_envelope(&a_bytes, a_root).unwrap();
        let stitch = stitch_umem_forks(&base, &env_a, &world);

        // ua's branch claims to confer TWO caps: `doc_a` (held at the tip) and `not_held`
        // (absent from the tip view — the revoked-before-tip case the gate must drop).
        let conferred = vec![
            ConferredCap {
                target: doc_a,
                debit_reach: true,
            },
            ConferredCap {
                target: not_held,
                debit_reach: true,
            },
        ];
        // The SETTLEMENT-TIP view: ua holds doc_a but NOT `not_held`.
        let settlement_held = vec![ConferredCap {
            target: doc_a,
            debit_reach: true,
        }];

        let settled = settle_umem_stitch(stitch, &conferred, &settlement_held);
        assert_eq!(
            settled.admitted,
            vec![ConferredCap {
                target: doc_a,
                debit_reach: true
            }],
            "the cap still held at the tip is admitted (the gate is non-vacuous)"
        );
        assert_eq!(
            settled.dropped,
            vec![ConferredCap {
                target: not_held,
                debit_reach: true
            }],
            "the cap not held at the tip is LINEAR-DROPPED (settlement-sound)"
        );
        // State pushout untouched by the gate; settles (no conflict) ⇒ a binding settled root.
        assert!(settled.settles(), "no state conflict ⇒ settles");
        assert!(
            settled.settled_root().is_some(),
            "a settled stitch has a binding root"
        );
    }

    /// The held view read FROM the live world reflects revocation: after a real
    /// `RevokeCapability` turn, the revoked target is structurally absent from
    /// [`settlement_held_at_tip`], so the same conferred cap flips admitted → dropped.
    #[test]
    fn settlement_held_at_tip_reflects_a_real_revocation() {
        use crate::world::revoke_capability;
        let (mut world, _room, ua, _ub, shared, doc_a, _gift) = mp_world();
        // ua holds caps to `shared` (slot 0) and `doc_a` (slot 1) at the tip.
        let before = settlement_held_at_tip(&world, ua);
        assert!(
            before.iter().any(|c| c.target == doc_a),
            "ua holds doc_a before the revoke"
        );
        // Find the slot of ua's doc_a cap and revoke it via a REAL verified turn on main.
        let slot = world
            .ledger()
            .get(&ua)
            .unwrap()
            .capabilities
            .iter()
            .find(|c| c.target == doc_a)
            .map(|c| c.slot)
            .expect("ua's doc_a cap slot");
        assert!(
            world
                .commit_turn(world.turn(ua, vec![revoke_capability(ua, slot)]))
                .is_committed(),
            "ua revokes her own doc_a cap with a real verified turn (the non-monotone op)"
        );
        let after = settlement_held_at_tip(&world, ua);
        assert!(
            !after.iter().any(|c| c.target == doc_a),
            "after the revoke, doc_a is GONE from the settlement-tip held view"
        );
        // shared is still held — only the revoked target left.
        assert!(
            after.iter().any(|c| c.target == shared),
            "the un-revoked cap (shared) survives at the tip"
        );
    }

    /// The anti-substitution root tooth fails closed (the same discipline as the cell +
    /// card membranes): a tampered projection is refused against the original root, but
    /// opens against its own root (a binding check, not a blanket reject); garbage bytes
    /// are refused.
    #[test]
    fn anti_substitution_umem_root_tooth_fails_closed() {
        let (world, room, _ua, _ub, _shared, doc_a, _db) = mp_world();
        let mut fork = world.fork();
        let _ = fork.commit_turn(fork.turn(_ua, vec![set_field(doc_a, 0, [0xAA; 32])]));
        let (bytes, root) = UmemEnvelope::seal(UmemBranch::mint(&fork, room, 3));

        // (1) GENUINE: opens and re-derives the claimed root.
        let env = open_umem_envelope(&bytes, root).expect("genuine envelope opens");
        assert_eq!(env.umem_root(), root);

        // (2) SUBSTITUTION: tamper a carried address value WITHOUT updating the root.
        let mut tampered = env.clone();
        tampered.branch.umem.insert(
            UKey::Field {
                cell: doc_a,
                slot: 0,
            },
            UVal::Bytes32([0xFF; 32]),
        );
        let tampered_bytes = tampered.to_bytes();
        assert_eq!(
            open_umem_envelope(&tampered_bytes, root),
            Err(UmemMembraneError::RootMismatch),
            "a substituted projection is REFUSED against the original root (fail-closed)"
        );
        // It opens against ITS OWN (recomputed) root — the tooth binds bytes↔root.
        let retampered_root = tampered.branch.umem_root();
        let mut fixed = tampered.clone();
        fixed.claimed_root = retampered_root;
        assert!(
            open_umem_envelope(&fixed.to_bytes(), retampered_root).is_ok(),
            "the tooth binds projection↔root, not a blanket reject"
        );

        // (3) MALFORMED: garbage bytes are refused.
        assert_eq!(
            open_umem_envelope(b"\xff\x00 not a postcard umem envelope", root),
            Err(UmemMembraneError::MalformedEnvelope),
            "malformed wire bytes are refused (fail-closed)"
        );
    }
}
