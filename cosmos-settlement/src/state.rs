use cosmwasm_schema::cw_serde;
use cw_storage_plus::{Item, Map};

/// Immutable-after-instantiation config: the pinned genesis anchor + VK hash.
#[cw_serde]
pub struct Config {
    pub genesis_lanes: [u32; 8],
    /// Hex, 32 bytes.
    pub verifying_key_hash: String,
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
