//! # realm-model — the expensive-to-retrofit MUD substrate, as ONE coherent model.
//!
//! `docs/design/HOARDLIGHT-LIVING-WORLD.md` §9 names three decisions that are
//! *cheap to make now and expensive to remove after players, assets, and
//! historical receipts depend on them*. This crate makes all three as ONE model
//! — they are interdependent (an identity acts in an instance of a realm whose
//! catalog gates the law the turn cites), so a single crate defines them with a
//! consistent interface instead of three lanes inventing incompatible ones.
//!
//! | doc § | decision | this crate |
//! |---|---|---|
//! | §9.4 | persistent **REALM** vs child **INSTANCE** as separate first-class objects | [`Realm`], [`Instance`], [`world::RealmWorld::open_instance`] / [`world::RealmWorld::settle_instance`] |
//! | §9.5 | a canonical **IDENTITY** the surfaces DERIVE from, not the reverse | [`CanonicalIdentity`], [`SurfaceRef`], [`world::RealmWorld::resolve_surface`] |
//! | §9.2 | the **RULESET CATALOG** = committed active-ruleset-roots = shared law | [`RulesetCatalog`], [`world::RealmWorld::admit`] |
//!
//! ## It composes with the ground truth, it does not reinvent it
//!
//! Every object here is a real [`dregg_cell::Cell`] on a real
//! [`dregg_cell::Ledger`] — the same primitives `node/src/mud_e2e.rs` and
//! `node/src/shared_world.rs` use. A realm turn carries
//! [`dregg_turn::action::Effect`] (the exact `Effect::SetField` mud_e2e fires).
//! Cell ids derive with [`derive_cell_id`], mirroring the node's
//! `spawned_cell_for(seed)` = `derive_raw(blake3(seed), default_token)`. So:
//!
//! * a **realm** is what `mud_e2e`'s hosted world BECOMES when it persists — a
//!   durable cell whose state outlives any one session;
//! * an **instance** is what a `mud_e2e` DUNGEON FORK becomes when it is named as
//!   protocol: a scoped child cell that pins a parent root at birth and settles a
//!   certified result back on finalize;
//! * an **identity** is what a `shared_world` key-ceremony participant RESOLVES
//!   to: one durable canonical object the per-surface bindings point at.
//!
//! ## What is a working model, what is a prototype, what is ember's call
//!
//! See `docs/design/MUD-SUBSTRATE.md`. In one line: the objects and their
//! cell-backed state + the admission gate are a **working model** driven by
//! `tests/driven.rs`; the *committed-law enforcement point* is modeled HERE in
//! [`world::RealmWorld::admit`] but in production belongs inside the executor's
//! proof-verify path (named in the doc).
//!
//! ⚑ The dependency this line used to name as missing — "durable realm
//! persistence depends on a node-served **receipt chain** that does not yet
//! exist" — is **BUILT**, and this crate is its consumer. `persist`'s
//! `RECEIPT_CHAIN` (`persist/src/tables.rs:295`) plus
//! `install_receipt_chain_durability` (`node/src/state.rs:914`) are driven by
//! `receipt_chain_and_mmr_head_survive_node_restart` (`node/src/state.rs:3727`),
//! and `node/src/realm_service.rs` rides the same durable-append discipline for
//! the realm substrate on `persist`'s `REALM_LOG` (`persist/src/tables.rs:314`),
//! replayed fail-closed by `NodeRealms::restore`. What remains modeled is the
//! *kernel* enforcement point above: `ruleset_root` is still absent from
//! `dregg_turn::Turn`, so a `/realm/*` turn is gate-routed by the node, not by
//! the executor's proof-verify path (`docs/design/DESIGN-realm-kernel-perimeter.md`).

pub mod catalog;
pub mod identity;
pub mod instance;
pub mod realm;
pub mod world;

pub use catalog::RulesetCatalog;
pub use identity::{CanonicalIdentity, Surface, SurfaceRef};
pub use instance::Instance;
pub use realm::Realm;
pub use world::{RealmReceipt, RealmTurn, RealmWorld, Refused};

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, CellId, Permissions};

/// A ruleset root — the 32-byte content address of a versioned body of law.
/// Opaque to the engine (a game, a balance table, a composition rule); the realm
/// catalog decides which roots are ADMITTED. Matches the `ruleset_root` public
/// input `param-compose` already binds (`param-compose/src/pi.rs`).
pub type RulesetRoot = [u8; 32];

/// The default token domain every cell in this model is derived + minted under —
/// byte-identical to `mud_e2e`'s `default_token_id()` so ids line up with the
/// existing world.
pub fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

/// Derive a deterministic [`CellId`] from a string seed, exactly as the node's
/// `deos.server.spawnCell(seed, ...)` / `spawned_cell_for(seed)` does: hash the
/// seed to a pubkey, then `derive_raw(pubkey, default_token)`.
pub fn derive_cell_id(seed: &str) -> CellId {
    let pubkey = *blake3::hash(seed.as_bytes()).as_bytes();
    CellId::derive_raw(&pubkey, &default_token_id())
}

/// The pubkey a seeded cell is minted under (so `Cell::with_balance(pubkey, ...)`
/// yields an id equal to [`derive_cell_id`] of the same seed).
pub fn derive_pubkey(seed: &str) -> [u8; 32] {
    *blake3::hash(seed.as_bytes()).as_bytes()
}

/// Pack a `u64` into a [`FieldElement`] (LE low 8 bytes) — the mud_e2e convention.
pub fn pack_u64(v: u64) -> FieldElement {
    dregg_cell::field_from_u64(v)
}

/// Read a `u64` back out of a [`FieldElement`] — the u64 lane (BE bytes `24..32`).
pub fn unpack_u64(fe: &FieldElement) -> u64 {
    dregg_cell::field_to_u64(fe)
}

/// Fully-open permissions — the mud_e2e `open_permissions()`. Authority in this
/// model is enforced by the realm admission gate (identity resolution + catalog
/// law), not by per-cell auth; a production wiring maps the caps onto real
/// [`Permissions`] (see the design doc's node wiring section).
pub fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}
