//! The settlement instruction processor -- the Solana twin of `DreggSettlement`
//! (`chain/contracts/DreggSettlement.sol`) and its Rust origin
//! `bridge/src/ethereum.rs::{EthBridgeState, submit_eth_settlement}`.
//!
//! `settle` reproduces the EVM state machine exactly:
//!   1. every one of the 25 lanes is a canonical BabyBear residue,
//!   2. `num_turns >= 1` (strictly monotone height),
//!   3. continuity: the proof's genesis lanes equal the current proven root,
//!   4. the Groth16 pairing check (commitment PoK + proof), fail-closed,
//!   5. advance: proven_root <- final_root, proven_height += num_turns.
//! A forged proof fails step 4 and the root does NOT advance.

use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint::ProgramResult,
    program::invoke_signed,
    pubkey::Pubkey,
    rent::Rent,
    system_instruction,
    sysvar::Sysvar,
};

use crate::error::SettlementError;
use crate::groth16::{self, Proof};
use crate::instruction::SettlementInstruction;
use crate::state::{is_canonical_lane, SettlementState, STATE_LEN};
use crate::vk::NUM_PUBLIC_INPUTS;
use crate::SEED_SETTLEMENT;

pub fn process(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    match SettlementInstruction::unpack(instruction_data)? {
        SettlementInstruction::InitSettlement {
            genesis_root,
            vk_hash,
        } => init(program_id, accounts, genesis_root, vk_hash),
        SettlementInstruction::Settle {
            a,
            b,
            c,
            commitment,
            commitment_pok,
            inputs,
        } => settle(
            program_id,
            accounts,
            &Proof {
                a,
                b,
                c,
                commitment,
                commitment_pok,
            },
            &inputs,
        ),
    }
}

/// Derive the settlement state PDA and assert the passed account matches it.
fn expect_settlement_pda(program_id: &Pubkey, key: &Pubkey) -> Result<u8, SettlementError> {
    let (pda, bump) = Pubkey::find_program_address(&[SEED_SETTLEMENT], program_id);
    if &pda != key {
        return Err(SettlementError::AccountState);
    }
    Ok(bump)
}

// ---------------------------------------------------------------------------
// InitSettlement
// ---------------------------------------------------------------------------

/// Accounts (in order):
///   0. `[signer, writable]` payer (funds the created account)
///   1. `[writable]`         settlement state PDA `[b"settlement"]` (created, program-owned)
///   2. `[]`                 System program
fn init(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    genesis_root: [u32; 8],
    vk_hash: [u8; 32],
) -> ProgramResult {
    let ai = &mut accounts.iter();
    let payer = next_account_info(ai)?;
    let state_ai = next_account_info(ai)?;
    let system_program = next_account_info(ai)?;

    if !payer.is_signer {
        return Err(SettlementError::MissingSigner.into());
    }
    let bump = expect_settlement_pda(program_id, state_ai.key)?;

    // Fresh init only: the PDA must not already carry state.
    if !state_ai.data_is_empty() {
        return Err(SettlementError::AlreadyInitialized.into());
    }

    // Fail-closed: a non-canonical genesis lane or a zero VK hash is refused
    // (mirrors the EVM constructor's `_requireCanonical` + `ZeroVerifyingKeyHash`).
    for l in &genesis_root {
        if !is_canonical_lane(*l) {
            return Err(SettlementError::NonCanonicalLane.into());
        }
    }
    if vk_hash == [0u8; 32] {
        return Err(SettlementError::InvalidGenesis.into());
    }

    // Create the program-owned state account.
    if system_program.key != &solana_program::system_program::id() {
        return Err(SettlementError::AccountState.into());
    }
    let rent = Rent::get()?;
    let lamports = rent.minimum_balance(STATE_LEN);
    let ix = system_instruction::create_account(
        payer.key,
        state_ai.key,
        lamports,
        STATE_LEN as u64,
        program_id,
    );
    invoke_signed(
        &ix,
        &[payer.clone(), state_ai.clone(), system_program.clone()],
        &[&[SEED_SETTLEMENT, &[bump]]],
    )?;

    // The genesis anchor is pinned AT INIT (mirrors `EthBridgeState::new`): the
    // first settle chains from it exactly like every later settle.
    let state = SettlementState {
        proven_height: 0,
        proven_root: genesis_root,
        genesis_root,
        vk_hash,
    };
    state.pack_into(&mut state_ai.data.borrow_mut())?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Settle
// ---------------------------------------------------------------------------

/// Accounts (in order):
///   0. `[writable]` settlement state PDA `[b"settlement"]` (program-owned)
fn settle(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    proof: &Proof,
    inputs: &[[u8; 32]; NUM_PUBLIC_INPUTS],
) -> ProgramResult {
    let ai = &mut accounts.iter();
    let state_ai = next_account_info(ai)?;

    expect_settlement_pda(program_id, state_ai.key)?;
    if state_ai.owner != program_id {
        return Err(SettlementError::AccountState.into());
    }

    let mut state = SettlementState::unpack(&state_ai.data.borrow())?;

    // (1) Every lane a canonical BabyBear residue; assemble the 25 lanes in the
    //     pinned order genesis[0..8) || final[8..16) || num_turns[16] ||
    //     chain_digest[17..25).
    let mut lanes = [0u32; NUM_PUBLIC_INPUTS];
    for (i, input) in inputs.iter().enumerate() {
        lanes[i] = input_to_lane(input)?;
    }
    let genesis_lanes: [u32; 8] = lanes[0..8].try_into().unwrap();
    let final_lanes: [u32; 8] = lanes[8..16].try_into().unwrap();
    let num_turns = lanes[16];

    // (2) Monotone height: num_turns must be >= 1 (EVM `ZeroTurns`).
    if num_turns == 0 {
        return Err(SettlementError::ZeroTurns.into());
    }

    // (3) Continuity: the proof's genesis lanes must equal the current proven root
    //     (EVM `ContinuityBroken`). The genesis anchor was pinned at init.
    if genesis_lanes != state.proven_root {
        return Err(SettlementError::ContinuityBroken.into());
    }

    // (4) The Groth16 pairing check (Pedersen commitment PoK + proof). A false /
    //     erroring verify rejects (fail closed) -- a FORGED proof stops here.
    groth16::verify(proof, inputs).map_err(|_| SettlementError::ProofRejected)?;

    // (5) Advance. proven_root <- final_root, proven_height += num_turns.
    state.proven_root = final_lanes;
    state.proven_height = state.proven_height.saturating_add(num_turns as u64);
    state.pack_into(&mut state_ai.data.borrow_mut())?;
    Ok(())
}

/// Interpret a 32-byte big-endian public input as a canonical BabyBear lane, or
/// reject it (`NonCanonicalLane`). A value `>= 2^32` (any non-zero high byte) or
/// `>= p` is non-canonical -- the stricter twin of the EVM `_requireCanonical`.
fn input_to_lane(input: &[u8; 32]) -> Result<u32, SettlementError> {
    if input[..28].iter().any(|&b| b != 0) {
        return Err(SettlementError::NonCanonicalLane);
    }
    let v = u32::from_be_bytes(input[28..32].try_into().unwrap());
    if !is_canonical_lane(v) {
        return Err(SettlementError::NonCanonicalLane);
    }
    Ok(v)
}
