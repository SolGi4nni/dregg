use cosmwasm_schema::cw_serde;
use cw_storage_plus::{Item, Map};

/// Immutable-after-instantiation config: the pinned genesis anchor.
///
/// ⚑ FLAG DAY 2026-07-30 — `verifying_key_hash: String` IS GONE. It stored
/// whatever the instantiator passed (checked only for "not all zeros") and was
/// read by exactly one query and by nothing else — `settle` never consulted it.
/// A stored pin can disagree with the key; the key this contract verifies
/// against is `crate::vk`, compiled in, so the only honest answer to "which key
/// is this?" is computed FROM `crate::vk`. `QueryMsg::VerifyingKeyHash` now
/// reads `vk::VK_DIGEST` directly and `instantiate` REFUSES a declaration that
/// disagrees with it, which is what makes the declaration mean something.
///
/// A stored `Config` from before this change fails to deserialize (the field is
/// required), so an old instance refuses to load rather than reinterpreting.
#[cw_serde]
pub struct Config {
    pub genesis_lanes: [u32; 8],
}

/// The advancing head: the current proven root lanes + cumulative height.
#[cw_serde]
pub struct Head {
    pub proven_lanes: [u32; 8],
    pub proven_height: u64,
}

pub const CONFIG: Item<Config> = Item::new("config");
pub const HEAD: Item<Head> = Item::new("head");

/// Every dregg state root this contract has ever proven (packLanes hex key ->
/// true), including the genesis anchor. Historical roots stay queryable so a
/// cross-chain verifier can check a message against the root proven at dispatch
/// time — the exact rationale as the EVM `_provenRoots` mapping.
pub const PROVEN_ROOTS: Map<&str, bool> = Map::new("proven_roots");
