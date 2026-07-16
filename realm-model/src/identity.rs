//! §9.5 — Canonical identity, surfaces DERIVE from it (not the reverse).
//!
//! > Do NOT make the first Discord ID the world identity. [...] The surface IDs
//! > (Discord user, WeChat OpenID, a web session) DERIVE from / bind to it, not
//! > the reverse.
//!
//! The object a `shared_world` key-ceremony participant should resolve TO.
//!
//! ## The direction is the whole point
//!
//! A [`CanonicalIdentity`] is a durable object minted from a principal key. It
//! exists FIRST. A [`SurfaceRef`] (a Discord user id, a web session, a WeChat
//! OpenID) is bound onto an already-existing canonical identity: the binding is
//! a real cell whose *entire state* is the canonical id it points at. Resolving
//! a surface reads that cell → the canonical id. There is deliberately NO
//! `identity_from_surface(discord_id)` constructor: a surface can only be bound
//! to a canonical identity that was minted independently, so the surface is
//! DERIVED (points at) and the canonical identity is PRIMARY.
//!
//! Because the binding cell's state literally holds the canonical id, two
//! different surfaces bound to the same identity resolve to the SAME 32 bytes —
//! that is "one identity across surfaces", cell-backed and non-vacuous.

use dregg_cell::CellId;

/// A surface an actor arrives on. Engine-general: the model does not privilege
/// any one (there is no "Discord is the account"); each is a peer binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Surface {
    Discord,
    Web,
    Telegram,
    WeChat,
    Native,
    /// An engine-general escape hatch for a surface the enum does not name yet.
    Other,
}

/// A reference to an actor AS SEEN on one surface: `(surface, surface-local id)`.
/// e.g. `(Discord, "user#12345")`, `(Web, "session-abcdef")`. This is the
/// per-surface identity `dreggnet-offerings`' viewer currently IS — the thing
/// this model resolves to a canonical identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SurfaceRef {
    pub surface: Surface,
    pub local: String,
}

impl SurfaceRef {
    pub fn new(surface: Surface, local: impl Into<String>) -> Self {
        SurfaceRef {
            surface,
            local: local.into(),
        }
    }

    /// The deterministic seed of the BINDING cell for this surface ref. A
    /// binding cell's state holds the canonical id it derives from.
    pub(crate) fn binding_seed(&self) -> String {
        format!("realm-surface-binding:{:?}:{}", self.surface, self.local)
    }
}

/// The canonical, durable principal. Usable across games, surfaces, and realms.
/// Its `id` is a stable cell handle; surface bindings, assets, authorship,
/// guilds, votes, and runs all resolve THROUGH this — the "one identity spine"
/// (§6) reduced to its irreducible core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalIdentity {
    /// The durable cell handle. Stable across surface rebindings and key
    /// rotation (rotation is a NAMED decision-for-ember — see the design doc).
    pub id: CellId,
    /// The principal public key this identity was minted from. In this model
    /// the id is `derive_raw(principal_pk, default_token)`; a production
    /// identity should use the hybrid PQ derivation
    /// (`CellId::derive_hybrid_raw`) — flagged in the doc.
    pub principal_pk: [u8; 32],
    /// A human-meaningful label for the principal (NOT a surface id).
    pub label: String,
}
