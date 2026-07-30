use cosmwasm_schema::{cw_serde, QueryResponses};

/// Pinned at instantiation — the on-chain twin of the `DreggSettlement`
/// constructor: the genesis anchor is authenticated by the deployer, NOT by
/// whoever settles first (a first-caller-establishes model would let any holder
/// of a valid proof over the same VK front-run and anchor a foreign chain).
#[cw_serde]
pub struct InstantiateMsg {
    /// The 8 BabyBear lanes of the genesis state root (pinned anchor).
    pub genesis_root: [u32; 8],
    /// The instantiator's DECLARATION of which verifying key this contract
    /// checks against: 32 bytes of hex, `0x` prefix optional, case-insensitive.
    ///
    /// ⚑ It MUST equal `vk::VK_DIGEST` — keccak256 over the canonical
    /// serialization of the key in `vk.rs` — or instantiation fails with
    /// `VkDigestMismatch`. It is CONSUMED by that check, never stored; query
    /// `VerifyingKeyHash` answers from `vk::VK_DIGEST` directly.
    ///
    /// Until 2026-07-30 this was checked only for "not all zeros" and then
    /// written to storage unexamined, which made it a field the caller filled
    /// in rather than a commitment. Mirrors `DreggSettlement.sol`'s constructor
    /// argument and Solana `InstructionData::InitSettlement { vk_hash }`.
    pub verifying_key_hash: String,
}

/// A dregg settlement: a real Groth16 proof + the 25-lane public statement,
/// split into its named lanes (the Cosmos twin of `DreggSettlement.settle`).
///
/// Curve coordinates are decimal strings (BN254 base-field integers), the exact
/// shape of `chain/test/fixtures/settlement_groth16.json`.
#[cw_serde]
pub enum ExecuteMsg {
    Settle {
        /// [A.x, A.y, B.x.c1, B.x.c0, B.y.c1, B.y.c0, C.x, C.y]
        proof: [String; 8],
        /// The single Pedersen commitment [Cm.x, Cm.y].
        commitments: [String; 2],
        /// The commitment proof-of-knowledge [Pok.x, Pok.y].
        commitment_pok: [String; 2],
        /// Public lanes 0..8 — the proof's genesis root (must chain continuity).
        genesis_root: [u32; 8],
        /// Public lanes 8..16 — the new proven root.
        final_root: [u32; 8],
        /// Public lane 16 — turns advanced (must be > 0).
        num_turns: u32,
        /// Public lanes 17..25 — the segment chain digest.
        chain_digest: [u32; 8],
    },
}

#[cw_serde]
#[derive(QueryResponses)]
pub enum QueryMsg {
    /// The current proven root as a `packLanes` hex key.
    #[returns(RootResponse)]
    ProvenRoot {},
    /// The current proven root as its 8 lanes.
    #[returns(LanesResponse)]
    ProvenRootLanes {},
    /// Total turns proven since genesis.
    #[returns(HeightResponse)]
    ProvenHeight {},
    /// The pinned genesis anchor as a `packLanes` hex key.
    #[returns(RootResponse)]
    GenesisAnchor {},
    /// Whether `root` (a `packLanes` hex key) has ever been proven.
    #[returns(BoolResponse)]
    IsProvenRoot { root: String },
    /// The pinned verifying-key hash.
    #[returns(RootResponse)]
    VerifyingKeyHash {},
}

#[cw_serde]
pub struct RootResponse {
    /// Hex-encoded 32-byte key.
    pub root: String,
}

#[cw_serde]
pub struct LanesResponse {
    pub lanes: [u32; 8],
}

#[cw_serde]
pub struct HeightResponse {
    pub height: u64,
}

#[cw_serde]
pub struct BoolResponse {
    pub value: bool,
}
