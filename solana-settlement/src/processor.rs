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
use crate::state::{
    is_canonical_lane, packed_root, ProvenRootMarker, SettlementState, MARKER_LEN, STATE_LEN,
};
use crate::vk::{self, NUM_PUBLIC_INPUTS};
use crate::{SEED_PROVEN_ROOT, SEED_SETTLEMENT};

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
            lanes,
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
            &lanes,
        ),
        SettlementInstruction::AssertProvenRoot { root } => {
            assert_proven_root(program_id, accounts, root)
        }
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

/// Derive the proven-root marker PDA for `packed` (a `packLanes` key).
fn proven_root_pda(program_id: &Pubkey, packed: &[u8; 32]) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[SEED_PROVEN_ROOT, packed], program_id)
}

/// Record a proven root in the registry: create its marker PDA (program-owned)
/// carrying `height`. Idempotent -- if the marker already exists (a root recurred,
/// e.g. a cycle), it is left as-is. The marker's existence is the Solana
/// `isProvenRoot`. `packed` is never `packLanes([0;8])` on a real path (a settle
/// records `final_root`, an init records the pinned genesis; the Nomad-law zero
/// root has no marker).
fn record_proven_root<'a>(
    program_id: &Pubkey,
    payer: &AccountInfo<'a>,
    marker_ai: &AccountInfo<'a>,
    system_program: &AccountInfo<'a>,
    packed: &[u8; 32],
    height: u64,
) -> ProgramResult {
    let (pda, bump) = proven_root_pda(program_id, packed);
    if &pda != marker_ai.key {
        return Err(SettlementError::UnprovenRoot.into());
    }
    // Idempotent: an already-recorded root stays recorded.
    if !marker_ai.data_is_empty() {
        return Ok(());
    }
    if system_program.key != &solana_program::system_program::id() {
        return Err(SettlementError::AccountState.into());
    }
    let rent = Rent::get()?;
    let lamports = rent.minimum_balance(MARKER_LEN);
    let ix = system_instruction::create_account(
        payer.key,
        marker_ai.key,
        lamports,
        MARKER_LEN as u64,
        program_id,
    );
    invoke_signed(
        &ix,
        &[payer.clone(), marker_ai.clone(), system_program.clone()],
        &[&[SEED_PROVEN_ROOT, packed, &[bump]]],
    )?;
    ProvenRootMarker { height }.pack_into(&mut marker_ai.data.borrow_mut())?;
    Ok(())
}

// ---------------------------------------------------------------------------
// InitSettlement
// ---------------------------------------------------------------------------

/// Accounts (in order):
///   0. `[signer, writable]` payer (funds the created accounts)
///   1. `[writable]`         settlement state PDA `[b"settlement"]` (created, program-owned)
///   2. `[writable]`         genesis proven-root marker PDA `[b"proven_root", packLanes(genesis)]`
///   3. `[]`                 System program
fn init(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    genesis_root: [u32; 8],
    vk_hash: [u8; 32],
) -> ProgramResult {
    let ai = &mut accounts.iter();
    let payer = next_account_info(ai)?;
    let state_ai = next_account_info(ai)?;
    let genesis_marker_ai = next_account_info(ai)?;
    let system_program = next_account_info(ai)?;

    if !payer.is_signer {
        return Err(SettlementError::MissingSigner.into());
    }
    let bump = expect_settlement_pda(program_id, state_ai.key)?;

    // Fresh init only: the PDA must not already carry state.
    if !state_ai.data_is_empty() {
        return Err(SettlementError::AlreadyInitialized.into());
    }

    // Fail-closed: a non-canonical genesis lane is refused (mirrors the EVM
    // constructor's `_requireCanonical`).
    for l in &genesis_root {
        if !is_canonical_lane(*l) {
            return Err(SettlementError::NonCanonicalLane.into());
        }
    }

    // Fail-closed: the pinned VK commitment must be the digest of the verifying key
    // THIS program verifies against (`vk_digest::compute() == vk::VK_DIGEST`, asserted
    // in tests/vk_pin.rs). The old check was `vk_hash != [0; 32]`, which accepted any
    // 32 bytes -- and the value everyone passed was `keccak256("dregg-settlement-vk-
    // dev-setup")`, a hash of a LABEL that stayed byte-identical across every possible
    // key regeneration. A pin that cannot move is not a pin; refusing anything but the
    // key's own digest is what makes it one.
    if vk_hash != vk::VK_DIGEST {
        return Err(SettlementError::VkDigestMismatch.into());
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

    // Record the genesis anchor in the proven-root registry (height 0), so the
    // first span's `genesisRoot` is `isProvenRoot` exactly like every later root.
    record_proven_root(
        program_id,
        payer,
        genesis_marker_ai,
        system_program,
        &packed_root(&genesis_root),
        0,
    )?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Settle
// ---------------------------------------------------------------------------

/// Accounts (in order):
///   0. `[writable]`         settlement state PDA `[b"settlement"]` (program-owned)
///   1. `[signer, writable]` payer (funds the new proven-root marker)
///   2. `[writable]`         final proven-root marker PDA `[b"proven_root", packLanes(final)]`
///   3. `[]`                 System program
fn settle(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    proof: &Proof,
    lanes: &[u32; NUM_PUBLIC_INPUTS],
) -> ProgramResult {
    let ai = &mut accounts.iter();
    let state_ai = next_account_info(ai)?;
    let payer = next_account_info(ai)?;
    let final_marker_ai = next_account_info(ai)?;
    let system_program = next_account_info(ai)?;

    if !payer.is_signer {
        return Err(SettlementError::MissingSigner.into());
    }
    expect_settlement_pda(program_id, state_ai.key)?;
    if state_ai.owner != program_id {
        return Err(SettlementError::AccountState.into());
    }

    let mut state = SettlementState::unpack(&state_ai.data.borrow())?;

    // (1) Every lane a canonical BabyBear residue. The lanes arrive in the pinned
    //     order genesis[0..8) || final[8..16) || num_turns[16] || chain_digest[17..25).
    for l in lanes.iter() {
        if !is_canonical_lane(*l) {
            return Err(SettlementError::NonCanonicalLane.into());
        }
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
    //     The MSM consumes 32-byte big-endian scalars, so the canonical u32 lanes
    //     are zero-extended back here. This reconstruction is EXACTLY the inverse of
    //     what the old wire encoding transmitted: `input_to_lane` used to reject any
    //     scalar whose high 28 bytes were non-zero, so those 700 bytes could never
    //     carry information and are now not sent (see instruction.rs's flag-day note).
    let inputs = lanes.map(lane_to_input);
    groth16::verify(proof, &inputs).map_err(|_| SettlementError::ProofRejected)?;

    // (5) Advance. proven_root <- final_root, proven_height += num_turns.
    state.proven_root = final_lanes;
    state.proven_height = state.proven_height.saturating_add(num_turns as u64);
    state.pack_into(&mut state_ai.data.borrow_mut())?;

    // (6) Record the new proven root in the registry so a fact proven under it
    //     stays queryable (`isProvenRoot`) even after a later span supersedes it
    //     -- the Solana twin of the EVM `_provenRoots` mapping.
    record_proven_root(
        program_id,
        payer,
        final_marker_ai,
        system_program,
        &packed_root(&final_lanes),
        state.proven_height,
    )?;
    Ok(())
}

/// **AssertProvenRoot** -- the CPI-able Solana `isProvenRoot` gate (the
/// `DreggProofISM` analog). Succeeds iff `root` (a `packLanes` key) was recorded
/// by a settlement: the passed marker account must be the registry PDA for
/// `root`, program-owned, and carry a valid marker. Reverts otherwise -- THE
/// NOMAD LAW: a zero/default/unrecorded root has no marker PDA and is refused, so
/// a consumer that CPIs this and proceeds only on success can never act on an
/// unproven root.
///
/// Accounts (in order):
///   0. `[]` the proven-root marker PDA `[b"proven_root", root]`
fn assert_proven_root(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    root: [u8; 32],
) -> ProgramResult {
    let ai = &mut accounts.iter();
    let marker_ai = next_account_info(ai)?;

    // The marker must be THE registry PDA for this exact root (binds the claimed
    // root to the account), program-owned (only a settlement writes it), and a
    // valid marker (rejects an all-zero / foreign account).
    let (pda, _bump) = proven_root_pda(program_id, &root);
    if &pda != marker_ai.key || marker_ai.owner != program_id || marker_ai.data_is_empty() {
        return Err(SettlementError::UnprovenRoot.into());
    }
    ProvenRootMarker::unpack(&marker_ai.data.borrow())?;
    Ok(())
}

/// Widen a canonical BabyBear lane to the 32-byte big-endian BN254 scalar the
/// public-input MSM consumes. Total (every `u32 < p < 2^31 < r`), and injective, so
/// the wire's u32 lanes and the MSM's scalars are in bijection -- carrying the
/// 28 leading zero bytes over the network bought nothing but 700 bytes of packet.
fn lane_to_input(lane: u32) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[28..].copy_from_slice(&lane.to_be_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reconstruction is exactly the old `input_to_lane`'s inverse on every
    /// value the old wire could legally carry: high 28 bytes zero, low 4 the lane.
    #[test]
    fn lane_to_input_is_the_old_decoders_inverse() {
        for lane in [0u32, 1, 7, 2013265920, u32::MAX] {
            let s = lane_to_input(lane);
            assert!(
                s[..28].iter().all(|&b| b == 0),
                "high 28 bytes are always zero"
            );
            assert_eq!(u32::from_be_bytes(s[28..].try_into().unwrap()), lane);
        }
    }

    #[test]
    fn non_canonical_lanes_are_still_refused() {
        assert!(!is_canonical_lane(2013265921), "p itself is not canonical");
        assert!(!is_canonical_lane(u32::MAX));
        assert!(is_canonical_lane(2013265920), "p-1 is");
    }
}
