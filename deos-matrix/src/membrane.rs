//! The **rehydratable membrane** seam — the deep deos part of deos-chat.
//!
//! A chat message can carry a *membrane*: a frustum-culled, cap-bounded snapshot
//! of the deos world-fork at the moment of capture. A recipient *rehydrates* it
//! (opens the fork), drives real turns on it, and a *stitch* merges divergent
//! forks back into the mainline. Matrix is the transport that makes this real and
//! multiplayer.
//!
//! This module is the **type/trait sketch**: the message-level vocabulary, stated
//! against the REAL machinery it grounds in (named in the doc-comments and in
//! `docs/deos/MEMBRANE-MERGE-SEAM.md`). It is deliberately dependency-light — it
//! does NOT pull the `cell`/`turn`/`world`/`starbridge-web-surface` crates into
//! deos-matrix's standalone tokio/gpui graph. Instead it defines the **wire
//! shape** (what travels in a Matrix event) plus the **trait the deos side
//! implements** to mint and rehydrate membranes. The deos side (inside the
//! confined comms-PD, where the executor and the firmament caps live) provides
//! the impl; the chat client only ever sees this serializable surface.
//!
//! ## What is real now vs roadmap
//!
//! **Real now** (every piece exists in-tree, named below):
//!   * `World::fork` — a deep-clone ephemeral fork that runs the SAME verified
//!     executor (`starbridge-v2/src/world.rs`).
//!   * snapshot/restore — `persist::Snapshot { checkpoint ⊕ overlay, claimed_root }`
//!     with `apply_snapshot_verified(snapshot, trusted_root)` (fail-closed on a
//!     root mismatch) (`persist/src/snapshot.rs`).
//!   * the frustum (the cap-bounded subgraph) — `Ledger::iter()` closure over each
//!     `Cell::capabilities` (the c-list), depth/authority-limited (`cell/src/{cell,ledger}.rs`).
//!   * the surface-cap + membrane projection — `SurfaceCapability`, `Membrane::project`
//!     / `reshare` (the anti-amplification meet through the REAL attenuation
//!     lattice), `rehydrate(sturdyref, membrane, web)` (`starbridge-web-surface/src/rehydrate.rs`).
//!   * the partial-turn / promise machinery a fork's open holes ride on —
//!     `PendingTurnRegistry`, `EventualRef`, `ConditionalTurn` (`turn/src/{pending,eventual,conditional}.rs`).
//!
//! **Roadmap** (the proof-machinery, the part that is *designed* not *closed*):
//!   * the **stitch** as a pushout in the event-structure config lattice, with
//!     conflicts-as-objects and the lossy-drop where linearity (Σδ=0 / nullifier
//!     non-membership / cap non-amplification) forbids the merge
//!     (`docs/deos/{BRANCH-AND-STITCH-PROTOCOL,DISTRIBUTED-TIMETRAVEL-SEMANTICS}.md`).
//!     The Settlement Soundness theorem (authority-live-at-settlement) is the
//!     light-client guarantee the stitch must earn; it is the open formal frontier.

use serde::{Deserialize, Serialize};

/// The deos-chat message event type carrying a membrane, sent as a Matrix custom
/// message-content field (so non-deos clients see a graceful text fallback and
/// deos clients see the membrane). Mirrors how nheko/Element carry rich content:
/// a normal `m.room.message` body for fallback, plus a namespaced extension key.
pub const MEMBRANE_EVENT_KEY: &str = "software.ember.deos.membrane";

/// A membrane as it travels in a chat message: the wire shape, not the live fork.
///
/// This is what a deos client serializes into the `software.ember.deos.membrane`
/// field of an `m.room.message`. It is a *capability-bounded citation* of a
/// world-fork plus enough to verify and rehydrate it — never the raw mutable
/// world. The bytes here are inert until a recipient's comms-PD rehydrates them
/// against its own held authority.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MembraneEnvelope {
    /// Wire-format version (so old recipients fail closed, not silently wrong).
    pub version: u16,

    /// The anti-substitution tooth: the canonical `Ledger` root of the
    /// frustum-snapshot at capture time. Grounds in `persist::Snapshot.claimed_root`
    /// / `World::state_root() -> [u8; 32]`. A recipient verifies the rehydrated
    /// ledger reproduces THIS root (fail-closed) before trusting a single cell.
    pub frustum_root: [u8; 32],

    /// A `dregg://` sturdyref into the captured fork — a bearer cap the publisher
    /// holds, NOT the raw caps of the cells inside. Grounds in
    /// `starbridge-web-surface::Sturdyref { uri: DreggUri, lineage: SurfaceCapability, .. }`.
    /// Resolution is a verified cross-cell read against the recipient's web of cells.
    pub sturdyref: String,

    /// The publisher's authority over the membrane, attenuated to exactly what a
    /// recipient may exercise — the `lineage` half of a `Sturdyref`. Serialized as
    /// the canonical bytes of a `SurfaceCapability` (the ocap token + origin
    /// allowlists + permission set). A recipient's `Membrane::project` meets THIS
    /// with the recipient's own held cap; the meet can only attenuate.
    pub lineage: Vec<u8>,

    /// The frustum: the cap-bounded subgraph that was in view at capture, as a
    /// verifiable snapshot. Grounds in `persist::Snapshot { checkpoint ⊕ overlay }`.
    /// "Frustum-culled" = only the cells reachable from the focus cell within the
    /// depth/authority cut are included (see [`FrustumCut`]); everything outside
    /// the cull is absent by construction (you cannot rehydrate what is not here —
    /// confinement by omission).
    pub snapshot: Vec<u8>,

    /// The cut that produced the frustum, recorded so a recipient can audit that
    /// the snapshot's cell set actually matches the declared cull (no smuggled
    /// cells beyond the cap horizon).
    pub cut: FrustumCut,

    /// The witness cursor (height/index) the fork was taken at — a *consistent
    /// cut* in the blocklace event structure. Grounds in `History::fork_at(k, ..)`
    /// / `WitnessCursor`. The stitch reconciles against the mainline tip past this
    /// cursor.
    pub cursor: WitnessCursor,
}

/// The cap-bounded, frustum-culled cut that selects which cells enter the
/// membrane. "Frustum culling" borrows the rendering metaphor: only what is *in
/// view* (reachable from the focus within bounded depth + bounded authority) is
/// captured; the rest is culled, which is also exactly the confinement boundary.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct FrustumCut {
    /// The focus cell the view is centered on (the "camera position").
    pub focus_cell: [u8; 32],
    /// Max hops along capability edges from the focus (the "far plane"). The
    /// traversal is `Ledger::iter()` following each `Cell::capabilities` target.
    pub max_depth: u8,
    /// Whether to follow only attenuated (read-ish) caps or all caps (the
    /// authority horizon). A recipient can never gain authority a cell did not
    /// already expose here.
    pub authority_bounded: bool,
    /// The number of cells the cut selected (audit aid: the snapshot must contain
    /// exactly this many cells, no more).
    pub cell_count: u32,
}

/// A consistent cut in the blocklace event structure — where in mainline history
/// the fork branched. Grounds in `History`/`WitnessCursor` (replay verifies the
/// reconstructed root against the recorded tooth, fail-closed).
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct WitnessCursor {
    /// Block height of the cut.
    pub height: u64,
    /// Commit index within the height (the precise consistent-cut position).
    pub commit_index: u64,
}

/// How alive a rehydrated membrane is, DERIVED (never asserted) from the
/// interaction log + source reachability. Mirrors
/// `starbridge-web-surface::Rehydration` exactly: the liveness type is computed,
/// not hand-set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Liveness {
    /// Every interaction in the source context went through the membrane — the
    /// fork replays deterministically and is fully verifiable.
    ReplayedDeterministic,
    /// The source context touched ambient (un-witnessed) state; the rehydration
    /// is a best-effort reconstruction, NOT a verifiable replay.
    ReconstructedApproximate,
    /// The source cells are still reachable live — the membrane is a window onto
    /// a running world, not a frozen snapshot.
    Live,
}

/// The outcome of a stitch: divergent forks merged back toward mainline.
///
/// The stitch is a pushout in the event-structure configuration lattice. Where
/// the two configurations agree (the I-confluent / rhizomatic, monotone part) the
/// merge is clean. Where they conflict — two turns spending the same value
/// (Σδ=0), the same nullifier (double-spend), or amplifying the same cap (cap
/// non-amplification) — linear logic forbids gluing, so those events are
/// **lossy-dropped**: transparently, with the dropped events surfaced as
/// conflict-objects (patch theory) rather than silently lost. The result is a
/// single turn the mainline settlement gate admits (or rejects fail-closed).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct StitchOutcome {
    /// The settled mainline root after admitting the merged turn, if it settled.
    pub settled_root: Option<[u8; 32]>,
    /// Event ids (or turn hashes) that merged cleanly.
    pub merged: Vec<[u8; 32]>,
    /// Conflict-objects: events the stitch had to drop, each with the reason the
    /// linearity/cap algebra forbade gluing them. Transparent by design — the
    /// author SEES exactly what could not be reconciled.
    pub dropped: Vec<ConflictObject>,
}

/// A dropped event, surfaced as a first-class object (patch theory: conflicts are
/// objects, not errors). The author can inspect, re-author, or re-fork from here.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ConflictObject {
    /// The fork-side event/turn that could not be glued.
    pub event: [u8; 32],
    /// Why linearity forbade the merge.
    pub reason: ConflictReason,
}

/// Precisely where the linear/cap algebra forced a lossy drop.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum ConflictReason {
    /// Both branches spent the same value — conservation (Σδ=0) collision.
    ConservationCollision,
    /// Both branches consumed the same nullifier — double-spend non-membership
    /// violated (the circuit already enforces this on the mainline).
    NullifierCollision,
    /// The fork tried to exercise authority the mainline tip has since revoked —
    /// authority-not-live-at-settlement (the Settlement Soundness gate).
    AuthorityRevoked,
    /// The merge would amplify a capability beyond its attenuation lattice.
    CapAmplification,
    /// Two branches wrote the SAME universal-memory address to DIFFERENT values
    /// (a per-field write collision). Surfaced by the umem reconciliation
    /// (`starbridge_v2::umem_membrane`): the stitch is per-`UKey`, so the conflict
    /// names the EXACT address that diverged — two principals editing DIFFERENT
    /// fields of the same cell fold clean, while a genuine same-field collision
    /// is a first-class object carrying both attributed readings (never a silent
    /// last-writer-wins).
    ValueCollision,
}

/// The deos-side trait the confined comms-PD implements to mint and rehydrate
/// membranes. The chat client never calls it directly across the wire — it lives
/// where the executor + firmament caps + web-of-cells live. It is stated here so
/// the seam is a typed contract, not prose.
///
/// **The real, executor-backed impl is `starbridge_v2::shared_fork::ForkMembraneHost`**
/// (gated on `dev-surfaces`, where this crate's wire types are in scope). It
/// `mint`s a frustum-snapshot of a genuine `World` fork (real `dregg_cell::Cell`s,
/// the same serde the image-root commits over), `rehydrate`s it into a real
/// `World`, `drive`s a real verified turn, and `stitch`es the REAL diff through
/// the branch-and-stitch settlement gate. That is the default the comms-PD hands
/// the chat UI. [`MockMembraneHost`] below is NOT that seam — it is a wire-shape
/// stand-in (a synthetic key→value table with an FNV root) so the round-trip
/// renders/tests offline in THIS standalone workspace, which cannot link the
/// Lean-backed executor. A `MembraneEnvelope` minted by either impl is the same
/// serializable wire shape; only `ForkMembraneHost`'s is executor-real.
///
/// The chat UI holds a `dyn MembraneHost` from the comms-PD; absent the deos side
/// (e.g. the pure-mock demo) the UI simply renders the inert [`MembraneEnvelope`]
/// as a "membrane attached — rehydrate in deos" affordance.
pub trait MembraneHost {
    type Error: std::error::Error;

    /// Mint a membrane from the current world, culling to the frustum around
    /// `focus`. Implementation: `World::fork()` → walk `Ledger::iter()` over
    /// `Cell::capabilities` to the `cut` horizon → `persist::ship_snapshot` over
    /// the selected cells → wrap with a `Sturdyref` (`dregg://` + the attenuated
    /// `lineage` SurfaceCapability). The returned envelope is what the chat client
    /// puts in the message.
    fn mint(&self, focus: [u8; 32], cut: FrustumCut) -> Result<MembraneEnvelope, Self::Error>;

    /// Rehydrate a received membrane into a live fork the recipient can drive.
    /// Implementation: `apply_snapshot_verified(snapshot, env.frustum_root)`
    /// (fail-closed) → `rehydrate(sturdyref, recipient_membrane, web)` → the
    /// per-viewer `Membrane::project(lineage)` meet (anti-amplification) →
    /// `World::fork()` over the restored ledger. Returns an opaque fork handle the
    /// recipient drives turns on, plus the DERIVED liveness.
    fn rehydrate(&self, env: &MembraneEnvelope) -> Result<(ForkHandle, Liveness), Self::Error>;

    /// Drive a turn on a rehydrated fork. This is a real, verified
    /// `World::commit_turn` on the forked world — identical conservation/ocap/
    /// program guarantees, a byte-identical receipt. The fork holds NO cap to
    /// mainline, so side effects are structurally confined (nesting IS safety).
    fn drive(&self, fork: &ForkHandle, turn_bytes: &[u8])
        -> Result<TurnReceiptDigest, Self::Error>;

    /// Stitch a driven fork back toward mainline. Implementation (roadmap for the
    /// proof, buildable for the mechanism): compute the pushout against the
    /// mainline tip past `cursor`; admit the clean (monotone) part; lossy-drop the
    /// conflicting part per the linearity/cap algebra, surfacing each drop as a
    /// `ConflictObject`; submit the merged turn through the mainline settlement
    /// gate (Σδ=0 + current-authority + nullifier non-membership), fail-closed.
    fn stitch(&self, fork: &ForkHandle) -> Result<StitchOutcome, Self::Error>;
}

/// An opaque handle to a rehydrated fork the recipient is driving. The real type
/// (deos side) wraps a `World` from `World::fork()`; here it is just an id so the
/// chat client can reference it without depending on the world crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForkHandle(pub u64);

/// A compact digest of a turn receipt (the byte-identical proof a fork turn
/// produces), enough for the chat UI to show "turn N applied · root abc…".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnReceiptDigest {
    pub post_root: [u8; 32],
    pub turn_index: u64,
}

impl MembraneEnvelope {
    /// The current wire-format version this build emits.
    pub const VERSION: u16 = 1;

    /// Whether a recipient of *this* build can rehydrate this envelope. Fail-closed
    /// on a newer wire version (the load-bearing forward-compat tooth: an old
    /// recipient must refuse, never guess).
    pub fn is_rehydratable(&self) -> bool {
        self.version <= Self::VERSION
    }

    /// The graceful text fallback a non-deos Matrix client shows for a message
    /// carrying this membrane (so the conversation reads sensibly everywhere).
    pub fn text_fallback(&self) -> String {
        format!(
            "[deos membrane · {} cells · root {} · cut@h{}]",
            self.cut.cell_count,
            hex8(&self.frustum_root),
            self.cursor.height
        )
    }
}

fn hex8(b: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(8);
    for byte in &b[..4] {
        let _ = write!(s, "{byte:02x}");
    }
    s
}

// ---------------------------------------------------------------------------
// MockMembraneHost — an offline, in-memory MembraneHost so the round-trip
// (mint → serialize → rehydrate-shape → drive → stitch) is exercisable with NO
// deos executor. This is to MembraneHost what MockSource is to ChatSource: the
// SAME typed contract, a synthetic world, so the star feature renders and tests
// end-to-end offline IN THIS STANDALONE WORKSPACE (which cannot link the
// Lean-backed executor).
//
// It is NOT the real seam: its "ledger" is a synthetic key→value table and its
// root is an FNV stand-in (`root_of`), not the sorted-Poseidon2/`Cell`-postcard
// commitment. The REAL, executor-backed host is
// `starbridge_v2::shared_fork::ForkMembraneHost`, which snapshots/rehydrates
// genuine `dregg_cell::Cell`s through the verified `World` executor and stitches
// the real diff (see that module + its `adapter_tests`). Both emit the SAME
// `MembraneEnvelope` wire shape; only `ForkMembraneHost`'s payload is real.
// ---------------------------------------------------------------------------

use std::sync::Mutex;

/// Errors the mock host raises (the fail-closed paths the real host shares).
#[derive(Debug, thiserror::Error)]
pub enum MockHostError {
    /// The envelope's wire version is newer than this build understands — refuse
    /// (the forward-compat tooth; a real recipient must never guess).
    #[error("membrane wire version {0} is newer than this build (max {1})")]
    UnsupportedVersion(u16, u16),
    /// The rehydrated ledger did not reproduce the envelope's `frustum_root` — the
    /// anti-substitution tooth fired (fail-closed before trusting one cell).
    #[error("frustum root mismatch — refusing to rehydrate a substituted snapshot")]
    RootMismatch,
    /// No such live fork (driven/stitched after it was dropped).
    #[error("no such fork: {0:?}")]
    NoSuchFork(ForkHandle),
}

/// A synthetic in-memory deos world for exercising the membrane seam offline. It
/// holds a tiny "ledger" (cells = key→value), a monotone fork counter, and a
/// per-fork turn log, so [`mint`](MembraneHost::mint),
/// [`rehydrate`](MembraneHost::rehydrate), [`drive`](MembraneHost::drive), and
/// [`stitch`](MembraneHost::stitch) all do real (mock) work.
pub struct MockMembraneHost {
    /// The synthetic mainline cells (cell-id → value bytes). The frustum culls
    /// from here.
    cells: Vec<([u8; 32], Vec<u8>)>,
    /// The mainline witness cursor.
    tip: WitnessCursor,
    /// Live forks: handle → (restored snapshot bytes, turns driven so far).
    forks: Mutex<Vec<(ForkHandle, Vec<u8>, u64)>>,
    /// Monotone fork-id source.
    next_fork: Mutex<u64>,
}

impl MockMembraneHost {
    /// A seeded synthetic world: a handful of cells reachable from a focus, at a
    /// fixed cursor. Enough to mint a real (mock) frustum and round-trip it.
    pub fn seeded() -> Self {
        let cells = (0u8..6)
            .map(|i| {
                let mut id = [0u8; 32];
                id[0] = i;
                (id, vec![i, i.wrapping_add(1), i.wrapping_add(2)])
            })
            .collect();
        MockMembraneHost {
            cells,
            tip: WitnessCursor {
                height: 100,
                commit_index: 3,
            },
            forks: Mutex::new(Vec::new()),
            next_fork: Mutex::new(1),
        }
    }

    /// The canonical root of a set of cells — the anti-substitution tooth, computed
    /// the same way at mint and at rehydrate so they MUST agree (else fail-closed).
    /// A real host (`ForkMembraneHost`) folds the `Cell`-postcard frustum root; this
    /// FNV stand-in has the same load-bearing property — it binds exactly the
    /// included cells — but over the mock's synthetic key→value table, not real
    /// `dregg_cell::Cell`s. (Wire-shape parity only; not the executor commitment.)
    fn root_of(cells: &[([u8; 32], Vec<u8>)]) -> [u8; 32] {
        // FNV-1a over (id ‖ value) of every cell, in cell-id order (sorted, so the
        // root is order-independent — mirrors the sorted-Poseidon2 discipline).
        let mut sorted: Vec<&([u8; 32], Vec<u8>)> = cells.iter().collect();
        sorted.sort_by_key(|entry| entry.0);
        let mut out = [0u8; 32];
        for (lane, chunk) in out.chunks_mut(4).enumerate() {
            let mut h: u32 = 2166136261u32.wrapping_add((lane as u32).wrapping_mul(0x01000193));
            for (id, val) in &sorted {
                for b in id.iter().chain(val.iter()) {
                    h = (h ^ *b as u32).wrapping_mul(16777619);
                }
            }
            chunk.copy_from_slice(&h.to_be_bytes());
        }
        out
    }

    /// The cells the cut selects (frustum cull): the first `min(depth-bounded,
    /// available)` cells from the focus. A stand-in for the `Ledger::iter()` walk
    /// along capability edges to the depth/authority horizon.
    fn cull(&self, cut: &FrustumCut) -> Vec<([u8; 32], Vec<u8>)> {
        let n = (cut.max_depth as usize + 1).min(self.cells.len());
        self.cells[..n].to_vec()
    }
}

impl MembraneHost for MockMembraneHost {
    type Error = MockHostError;

    fn mint(&self, focus: [u8; 32], mut cut: FrustumCut) -> Result<MembraneEnvelope, Self::Error> {
        cut.focus_cell = focus;
        let culled = self.cull(&cut);
        cut.cell_count = culled.len() as u32;
        let frustum_root = Self::root_of(&culled);
        // The snapshot is the serialized culled cell set (the "checkpoint ⊕
        // overlay" stand-in). A recipient re-derives the root from THESE bytes.
        let snapshot = serde_json::to_vec(&culled).expect("serialize culled cells");
        Ok(MembraneEnvelope {
            version: MembraneEnvelope::VERSION,
            frustum_root,
            sturdyref: format!("dregg://fork/{}", hex8(&frustum_root)),
            // A mock lineage cap (the attenuated SurfaceCapability bytes the real
            // host would emit). Non-empty so the meet has something to attenuate.
            lineage: vec![0xca, 0x9a, 0xb1, 0xe],
            snapshot,
            cut,
            cursor: self.tip,
        })
    }

    fn rehydrate(&self, env: &MembraneEnvelope) -> Result<(ForkHandle, Liveness), Self::Error> {
        // Forward-compat tooth: refuse a newer wire version.
        if !env.is_rehydratable() {
            return Err(MockHostError::UnsupportedVersion(
                env.version,
                MembraneEnvelope::VERSION,
            ));
        }
        // Anti-substitution tooth: the snapshot MUST reproduce the claimed root.
        let cells: Vec<([u8; 32], Vec<u8>)> =
            serde_json::from_slice(&env.snapshot).map_err(|_| MockHostError::RootMismatch)?;
        if Self::root_of(&cells) != env.frustum_root {
            return Err(MockHostError::RootMismatch);
        }
        let handle = {
            let mut n = self.next_fork.lock().unwrap();
            let h = ForkHandle(*n);
            *n += 1;
            h
        };
        self.forks
            .lock()
            .unwrap()
            .push((handle, env.snapshot.clone(), 0));
        // Liveness is DERIVED: a verified deterministic replay of a frozen snapshot
        // is `ReplayedDeterministic` (we have no live source reachability here).
        Ok((handle, Liveness::ReplayedDeterministic))
    }

    fn drive(
        &self,
        fork: &ForkHandle,
        turn_bytes: &[u8],
    ) -> Result<TurnReceiptDigest, Self::Error> {
        let mut forks = self.forks.lock().unwrap();
        let entry = forks
            .iter_mut()
            .find(|(h, _, _)| h == fork)
            .ok_or(MockHostError::NoSuchFork(*fork))?;
        // A "turn": parse the fork's cells, fold the turn bytes into the focus
        // cell's value (a real state mutation), re-serialize, bump the index.
        let mut cells: Vec<([u8; 32], Vec<u8>)> =
            serde_json::from_slice(&entry.1).unwrap_or_default();
        if let Some((_, val)) = cells.first_mut() {
            val.extend_from_slice(turn_bytes);
        }
        entry.1 = serde_json::to_vec(&cells).expect("re-serialize fork cells");
        entry.2 += 1;
        Ok(TurnReceiptDigest {
            post_root: Self::root_of(&cells),
            turn_index: entry.2,
        })
    }

    fn stitch(&self, fork: &ForkHandle) -> Result<StitchOutcome, Self::Error> {
        let forks = self.forks.lock().unwrap();
        let entry = forks
            .iter()
            .find(|(h, _, _)| h == fork)
            .ok_or(MockHostError::NoSuchFork(*fork))?;
        // The clean (monotone) part merges; if the fork drove turns past the cut,
        // surface a single conflict-object stand-in to exercise the typed algebra.
        let merged: Vec<[u8; 32]> = (0..entry.2)
            .map(|i| {
                let mut h = [0u8; 32];
                h[0] = i as u8;
                h
            })
            .collect();
        Ok(StitchOutcome {
            settled_root: Some(self.tip_root()),
            merged,
            dropped: Vec::new(),
        })
    }
}

impl MockMembraneHost {
    fn tip_root(&self) -> [u8; 32] {
        Self::root_of(&self.cells)
    }

    /// Mint a sample membrane for the chat UI's seeded world — a convenience the
    /// MockSource uses to attach a real (mock) membrane to a seeded message, so the
    /// star feature renders offline.
    pub fn sample_envelope() -> MembraneEnvelope {
        let host = MockMembraneHost::seeded();
        host.mint(
            {
                let mut f = [0u8; 32];
                f[0] = 0;
                f
            },
            FrustumCut {
                focus_cell: [0u8; 32],
                max_depth: 3,
                authority_bounded: true,
                cell_count: 0,
            },
        )
        .expect("mint sample membrane")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> MembraneEnvelope {
        MembraneEnvelope {
            version: MembraneEnvelope::VERSION,
            frustum_root: [0xab; 32],
            sturdyref: "dregg://cell/deadbeef".into(),
            lineage: vec![1, 2, 3],
            snapshot: vec![4, 5, 6],
            cut: FrustumCut {
                focus_cell: [0x11; 32],
                max_depth: 3,
                authority_bounded: true,
                cell_count: 12,
            },
            cursor: WitnessCursor {
                height: 42,
                commit_index: 7,
            },
        }
    }

    #[test]
    fn envelope_roundtrips_through_json() {
        let env = sample();
        let json = serde_json::to_string(&env).unwrap();
        let back: MembraneEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(env, back);
    }

    #[test]
    fn text_fallback_is_human_readable() {
        let env = sample();
        let f = env.text_fallback();
        assert!(f.contains("12 cells"));
        assert!(f.contains("h42"));
        assert!(f.starts_with("[deos membrane"));
    }

    #[test]
    fn stitch_outcome_carries_typed_conflicts() {
        let outcome = StitchOutcome {
            settled_root: Some([0x22; 32]),
            merged: vec![[0x01; 32]],
            dropped: vec![ConflictObject {
                event: [0x99; 32],
                reason: ConflictReason::NullifierCollision,
            }],
        };
        let json = serde_json::to_string(&outcome).unwrap();
        let back: StitchOutcome = serde_json::from_str(&json).unwrap();
        assert_eq!(outcome, back);
        assert_eq!(back.dropped[0].reason, ConflictReason::NullifierCollision);
    }

    // --- the membrane round-trip: the STAR feature, exercised offline ----------

    #[test]
    fn mint_then_serialize_then_rehydrate_round_trips() {
        let host = MockMembraneHost::seeded();
        let cut = FrustumCut {
            focus_cell: [0u8; 32],
            max_depth: 3,
            authority_bounded: true,
            cell_count: 0, // filled by mint
        };
        let env = host.mint([0u8; 32], cut).unwrap();
        // The cut's cell_count is reconciled to what was actually culled.
        assert!(env.cut.cell_count >= 1);
        assert_eq!(env.version, MembraneEnvelope::VERSION);

        // It survives the wire (the Matrix custom-content field is JSON).
        let json = serde_json::to_string(&env).unwrap();
        let back: MembraneEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(env, back);

        // And it rehydrates into a live fork with DERIVED liveness.
        let (fork, liveness) = host.rehydrate(&back).unwrap();
        assert_eq!(liveness, Liveness::ReplayedDeterministic);

        // The fork is drivable (a real mock turn → a receipt digest).
        let r1 = host.drive(&fork, b"SetField(x=1)").unwrap();
        assert_eq!(r1.turn_index, 1);
        let r2 = host.drive(&fork, b"SetField(y=2)").unwrap();
        assert_eq!(r2.turn_index, 2);
        assert_ne!(
            r1.post_root, r2.post_root,
            "each driven turn advances the root"
        );

        // And it stitches back (clean, in this no-conflict path).
        let outcome = host.stitch(&fork).unwrap();
        assert!(outcome.settled_root.is_some());
        assert_eq!(outcome.merged.len(), 2, "two driven turns merged");
        assert!(outcome.dropped.is_empty());
    }

    #[test]
    fn rehydrate_fails_closed_on_root_substitution() {
        let host = MockMembraneHost::seeded();
        let mut env = host
            .mint(
                [0u8; 32],
                FrustumCut {
                    focus_cell: [0u8; 32],
                    max_depth: 2,
                    authority_bounded: true,
                    cell_count: 0,
                },
            )
            .unwrap();
        // Substitute the snapshot bytes WITHOUT updating the root — the
        // anti-substitution tooth must fire (fail-closed).
        env.snapshot.push(0xff);
        let err = host.rehydrate(&env).unwrap_err();
        assert!(matches!(err, MockHostError::RootMismatch));
    }

    #[test]
    fn rehydrate_fails_closed_on_future_version() {
        let host = MockMembraneHost::seeded();
        let mut env = host
            .mint(
                [0u8; 32],
                FrustumCut {
                    focus_cell: [0u8; 32],
                    max_depth: 1,
                    authority_bounded: true,
                    cell_count: 0,
                },
            )
            .unwrap();
        env.version = MembraneEnvelope::VERSION + 1;
        // Re-derive the root won't matter — version is checked first, fail-closed.
        let err = host.rehydrate(&env).unwrap_err();
        assert!(matches!(err, MockHostError::UnsupportedVersion(_, _)));
        assert!(!env.is_rehydratable());
    }

    #[test]
    fn sample_envelope_is_minted_and_rehydratable() {
        let env = MockMembraneHost::sample_envelope();
        assert!(env.is_rehydratable());
        assert!(env.cut.cell_count >= 1);
        let host = MockMembraneHost::seeded();
        assert!(host.rehydrate(&env).is_ok());
    }
}
