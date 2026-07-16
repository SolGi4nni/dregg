//! §9.4 — the child INSTANCE (the scoped, disposable half of realm/instance).
//!
//! > An INSTANCE is a scoped/daily/seeded child of a realm. Model both as
//! > first-class, with the instance's relationship to its realm explicit (what
//! > persists vs what resets; how an instance's results settle back to the realm).
//!
//! What a `mud_e2e` DUNGEON FORK becomes when it is named as protocol rather than
//! left in a JavaScript host program (the doc's exact ask, §9.4). An instance is
//! a scoped child cell of a realm:
//!
//! * **pins a parent root at birth** — [`Instance::parent_pin`] snapshots the
//!   realm's durable value at open time. Whether the instance USES that pin (a
//!   fixed parent) or tracks the realm HEAD (a moving parent) is now the realm's
//!   OWN choice — its [`crate::realm::Membrane`] (ember's DECIDED per-realm
//!   membrane). The pin is always recorded at birth; a `PinAtBirth` realm reads
//!   it as the visible parent, a `MovingParent` realm reads the live head. See
//!   [`crate::world::RealmWorld::visible_parent`];
//! * **has its own scratch state** — the instance cell's fields; these RESET
//!   with the instance (a fresh instance = a fresh cell);
//! * **settles a certified result back** — on finalize, its result is applied to
//!   the realm cell (what PERSISTS), through the catalog-gated admission path.

use dregg_cell::CellId;

/// Field slots the instance cell stamps (its scoped, disposable scratch state).
pub mod field {
    /// 0 = open, 1 = finalized. Once finalized, the instance may not settle again.
    pub const STATUS: usize = 0;
    /// The certified result this instance will settle back to its realm.
    pub const RESULT: usize = 1;
    /// The parent realm value PINNED at birth (the membrane snapshot — what the
    /// child saw of its parent when it opened). LE-u64 for the demo accumulator.
    pub const PARENT_PIN: usize = 2;
}

/// Instance status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstanceStatus {
    Open,
    Finalized,
}

/// A scoped child of a realm. First-class and distinct in TYPE from a
/// [`crate::Realm`] — the §9.4 separation that makes "make it a MUD later" an
/// addition instead of a rewrite from per-session objects to durable ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instance {
    /// The instance's scoped cell handle. Derived from `(realm, seed)`.
    pub id: CellId,
    /// The realm this instance is a child of (the explicit parent link).
    pub realm: CellId,
    /// The immutable seed that scopes this instance (a day seed, a match seed).
    pub seed: String,
    /// The parent realm value this instance PINNED at birth. What the child saw
    /// of its parent; does not change if the realm advances underneath it.
    pub parent_pin: u64,
}
