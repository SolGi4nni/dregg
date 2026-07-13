//! # dregg settlement — the Cosmos-side verifier (CosmWasm)
//!
//! A CosmWasm contract that verifies a **real dregg Groth16 proof** natively
//! inside a Cosmos runtime. It is the Cosmos twin of the EVM `DreggSettlement.sol`
//! + its gnark-generated BN254 verifier: it takes the same proof, over the same
//! 25-lane public statement, verified against the same verifying key
//! (`chain/test/fixtures/settlement_groth16.json` — the fixture the Foundry EVM
//! test settles), and advances a `provenRoot` / `provenHeight` on accept.
//!
//! ## Why this works (the "path" answer)
//!
//! A CosmWasm contract IS Rust compiled to wasm, so a BN254 Groth16 verify runs
//! in it directly with arkworks (`ark-bn254`) — there is **no need for a
//! Cosmos-native (Pasta/field-parameterized) instantiation** to make Cosmos
//! verify a dregg proof. The SAME BN254 proof the EVM verifies is verified here;
//! only the verifier's host changes (a CosmWasm contract instead of an EVM
//! precompile). The gnark Pedersen-commitment gate is reproduced faithfully in
//! `verifier.rs`. (A field-parameterized native-hash shrink to Cosmos's own field
//! would only be a *gas* optimization, exactly as BN254 is the gas-right choice
//! on the EVM; it is not required for correctness.)
//!
//! ## Honest scope
//!
//! - The verifier + its accept/reject are **real** (a genuine two-pairing BN254
//!   Groth16 + Pedersen check; no mock on the accept path).
//! - The trusted setup is the **single-party dev ceremony** (the same VK as the
//!   EVM verifier) — real circuit, real verifier, toxic-waste-known dev setup.
//! - This is **test/local-demonstrated**, not deployed to a live Cosmos chain.
//! - The fuller **IBC light-client path** (a dregg proof arriving as an IBC packet
//!   / an ICS-08-style client verifying dregg headers) is **named, not built**:
//!   this contract is the CosmWasm-contract instantiation, which is the tractable
//!   demonstration that Cosmos verifies dregg for itself.

pub mod error;
pub mod msg;
pub mod state;
pub mod verifier;
pub mod vk;

use cosmwasm_std::{
    entry_point, to_json_binary, Binary, Deps, DepsMut, Env, MessageInfo, Response, StdResult,
};
use sha3::{Digest, Keccak256};

use error::ContractError;
use msg::{
    BoolResponse, ExecuteMsg, HeightResponse, InstantiateMsg, LanesResponse, QueryMsg, RootResponse,
};
use state::{Config, Head, CONFIG, HEAD, PROVEN_ROOTS};
use verifier::{RawProof, NUM_LANES};

/// BabyBear prime p = 2^31 - 2^27 + 1. Every lane must be < p (as in `DreggSettlement.sol`).
pub const BABYBEAR_P: u32 = 2_013_265_921;

/// `packLanes`: keccak256 over the tight 32-byte big-endian packing of the 8
/// lanes (lane i occupies bytes [4i, 4i+4)). Byte-identical to the Solidity
/// `packLanes` (`abi.encodePacked(uint32 × 8)` then keccak256), so a root packed
/// here matches the EVM index.
pub fn pack_lanes(lanes: &[u32; 8]) -> String {
    let mut buf = [0u8; 32];
    for (i, lane) in lanes.iter().enumerate() {
        buf[4 * i..4 * i + 4].copy_from_slice(&lane.to_be_bytes());
    }
    let digest = Keccak256::digest(buf);
    hex::encode(digest)
}

fn require_canonical(index: usize, value: u32) -> Result<(), ContractError> {
    if value >= BABYBEAR_P {
        return Err(ContractError::NonCanonicalLane { index, value });
    }
    Ok(())
}

#[entry_point]
pub fn instantiate(
    deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    msg: InstantiateMsg,
) -> Result<Response, ContractError> {
    if msg
        .verifying_key_hash
        .trim_start_matches("0x")
        .trim_matches('0')
        .is_empty()
    {
        return Err(ContractError::ZeroVerifyingKeyHash);
    }
    for (i, &lane) in msg.genesis_root.iter().enumerate() {
        require_canonical(i, lane)?;
    }

    CONFIG.save(
        deps.storage,
        &Config {
            genesis_lanes: msg.genesis_root,
            verifying_key_hash: msg.verifying_key_hash,
        },
    )?;
    HEAD.save(
        deps.storage,
        &Head {
            proven_lanes: msg.genesis_root,
            proven_height: 0,
        },
    )?;
    // Record the genesis anchor as a proven root (bytes32(0) is never recorded).
    PROVEN_ROOTS.save(deps.storage, &pack_lanes(&msg.genesis_root), &true)?;

    Ok(Response::new()
        .add_attribute("action", "instantiate")
        .add_attribute("genesis_root", pack_lanes(&msg.genesis_root)))
}

#[entry_point]
pub fn execute(
    deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    msg: ExecuteMsg,
) -> Result<Response, ContractError> {
    match msg {
        ExecuteMsg::Settle {
            proof,
            commitments,
            commitment_pok,
            genesis_root,
            final_root,
            num_turns,
            chain_digest,
        } => settle(
            deps,
            proof,
            commitments,
            commitment_pok,
            genesis_root,
            final_root,
            num_turns,
            chain_digest,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn settle(
    deps: DepsMut,
    proof: [String; 8],
    commitments: [String; 2],
    commitment_pok: [String; 2],
    genesis_root: [u32; 8],
    final_root: [u32; 8],
    num_turns: u32,
    chain_digest: [u32; 8],
) -> Result<Response, ContractError> {
    // 1. Canonicalize every lane and assemble the pinned 25-lane statement:
    //    genesis[0..8) ++ final[8..16) ++ numTurns[16] ++ chainDigest[17..25).
    let mut inputs = [0u64; NUM_LANES];
    for i in 0..8 {
        require_canonical(i, genesis_root[i])?;
        inputs[i] = genesis_root[i] as u64;
    }
    for i in 0..8 {
        require_canonical(8 + i, final_root[i])?;
        inputs[8 + i] = final_root[i] as u64;
    }
    require_canonical(16, num_turns)?;
    inputs[16] = num_turns as u64;
    for i in 0..8 {
        require_canonical(17 + i, chain_digest[i])?;
        inputs[17 + i] = chain_digest[i] as u64;
    }

    // 2. A settlement must advance the chain.
    if num_turns == 0 {
        return Err(ContractError::ZeroTurns);
    }

    // 3. Continuity: the proof's genesis lanes must equal the current proven root.
    let mut head = HEAD.load(deps.storage)?;
    if genesis_root != head.proven_lanes {
        return Err(ContractError::ContinuityBroken);
    }

    // 4. The real pairing check. Any failure (bad point, commitment, or pairing)
    //    is a hard reject — no state changes.
    let raw = RawProof {
        proof: [
            proof[0].as_str(),
            proof[1].as_str(),
            proof[2].as_str(),
            proof[3].as_str(),
            proof[4].as_str(),
            proof[5].as_str(),
            proof[6].as_str(),
            proof[7].as_str(),
        ],
        commitments: [commitments[0].as_str(), commitments[1].as_str()],
        commitment_pok: [commitment_pok[0].as_str(), commitment_pok[1].as_str()],
    };
    verifier::verify(&raw, &inputs)?;

    // 5. Effects: advance the head and record the new proven root.
    let old_key = pack_lanes(&head.proven_lanes);
    head.proven_lanes = final_root;
    head.proven_height += num_turns as u64;
    HEAD.save(deps.storage, &head)?;
    let new_key = pack_lanes(&final_root);
    PROVEN_ROOTS.save(deps.storage, &new_key, &true)?;

    Ok(Response::new()
        .add_attribute("action", "settle")
        .add_attribute("old_root", old_key)
        .add_attribute("new_root", new_key)
        .add_attribute("proven_height", head.proven_height.to_string())
        .add_attribute("num_turns", num_turns.to_string()))
}

#[entry_point]
pub fn query(deps: Deps, _env: Env, msg: QueryMsg) -> StdResult<Binary> {
    match msg {
        QueryMsg::ProvenRoot {} => {
            let head = HEAD.load(deps.storage)?;
            to_json_binary(&RootResponse {
                root: pack_lanes(&head.proven_lanes),
            })
        }
        QueryMsg::ProvenRootLanes {} => {
            let head = HEAD.load(deps.storage)?;
            to_json_binary(&LanesResponse {
                lanes: head.proven_lanes,
            })
        }
        QueryMsg::ProvenHeight {} => {
            let head = HEAD.load(deps.storage)?;
            to_json_binary(&HeightResponse {
                height: head.proven_height,
            })
        }
        QueryMsg::GenesisAnchor {} => {
            let cfg = CONFIG.load(deps.storage)?;
            to_json_binary(&RootResponse {
                root: pack_lanes(&cfg.genesis_lanes),
            })
        }
        QueryMsg::IsProvenRoot { root } => {
            let value = PROVEN_ROOTS.may_load(deps.storage, &root)?.unwrap_or(false);
            to_json_binary(&BoolResponse { value })
        }
        QueryMsg::VerifyingKeyHash {} => {
            let cfg = CONFIG.load(deps.storage)?;
            to_json_binary(&RootResponse {
                root: cfg.verifying_key_hash,
            })
        }
    }
}
