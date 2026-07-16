//! §9.4 — the persistent REALM (the durable half of realm/instance).
//!
//! > A REALM is the persistent shared world (durable, many participants,
//! > cross-session).
//!
//! What `mud_e2e`'s hosted world becomes when it PERSISTS. A realm is a single
//! durable cell: its state is the world state that outlives any one instance.
//! Instances are opened as children (see [`crate::instance`]) and settle
//! certified results back into this cell — so a realm accrues history across
//! sessions while each instance is disposable.

use dregg_cell::CellId;

/// Field slots the realm cell stamps (its durable world state). Engine-general:
/// these are the substrate's own bookkeeping, NOT game fields — a game's own
/// entity schemas live in other cells the realm's catalog admits law over.
pub mod field {
    /// How many instances have settled back into this realm (advances on every
    /// settle; the realm's "height" in the crude sense this model needs).
    pub const EPOCH: usize = 0;
    /// A durable accumulator instances contribute to when they settle — the
    /// stand-in for "what an instance's result adds to the persistent world"
    /// (a hoard total, a shared score, a season tally). Opaque to the engine.
    pub const HOARD: usize = 1;
    /// The realm's [`Membrane`] discriminant (0 = [`Membrane::PinAtBirth`],
    /// 1 = [`Membrane::MovingParent`]). This is COMMITTED realm state — the
    /// membrane is a PROPERTY of the realm, not a fixed engine policy — so a
    /// resolver reads a realm's observation semantics off its cell, and the
    /// property is load-bearing (flip it, and instance visibility flips).
    pub const MEMBRANE: usize = 2;
}

/// How an instance observes its parent realm during a run (ember's DECIDED
/// "Both": the membrane is a per-realm property, not one fixed engine policy).
///
/// The two variants answer the §9.4 open question — "child pins a parent root at
/// birth" vs "child observes a moving parent" — by making it the realm's OWN
/// choice, committed on the realm cell:
///
/// * [`Membrane::PinAtBirth`] — the instance snapshots the realm root at open;
///   realm changes during the run are INVISIBLE until settle. Deterministic and
///   replayable: a fair daily roguelite run (The Descent's daily seed) where two
///   players on the same seed must see the same world regardless of what the
///   shared realm did meanwhile. This is the original committed behavior.
/// * [`Membrane::MovingParent`] — the instance tracks the realm HEAD; realm
///   changes are visible as they happen. A live shared world (a persistent town
///   like Hearthspire) where an instance is a window onto the moving realm, not a
///   frozen snapshot. Settle-back becomes a live interaction against the current
///   head (see [`crate::world::RealmWorld::visible_parent`] and the OCC settle).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Membrane {
    /// Snapshot the realm root at birth; concurrent realm changes are invisible
    /// to the instance until it settles. Deterministic / replayable.
    PinAtBirth,
    /// Track the realm HEAD; the instance sees concurrent realm changes live.
    MovingParent,
}

impl Membrane {
    /// The committed discriminant stored in [`field::MEMBRANE`].
    pub fn as_u64(self) -> u64 {
        match self {
            Membrane::PinAtBirth => 0,
            Membrane::MovingParent => 1,
        }
    }

    /// Read a membrane back from its committed discriminant (anything other than
    /// `1` reads as [`Membrane::PinAtBirth`] — the conservative default).
    pub fn from_u64(v: u64) -> Self {
        match v {
            1 => Membrane::MovingParent,
            _ => Membrane::PinAtBirth,
        }
    }
}

/// The persistent shared world. First-class: it is an object with a stable id
/// and durable cell-backed state, distinct in TYPE from an [`crate::Instance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Realm {
    /// The durable realm cell handle. Derived from the realm name; stable across
    /// every instance opened under it.
    pub id: CellId,
    /// The realm's stable name (engine-general: "a realm", not "Hearthspire").
    pub name: String,
    /// The realm's ruleset catalog cell — the committed active law (§9.2). Held
    /// as a sibling cell so the catalog is COMMITTED STATE, not host config.
    pub catalog: CellId,
    /// How this realm's instances observe it (ember's DECIDED per-realm membrane).
    /// Mirrors the committed [`field::MEMBRANE`] value on the realm cell; the
    /// authority is the cell, this struct field is a convenience mirror.
    pub membrane: Membrane,
}
