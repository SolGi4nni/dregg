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
}
