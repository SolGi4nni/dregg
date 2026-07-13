//! # dregg Solana settlement program (native, no Anchor)
//!
//! The Solana ON-CHAIN analog of `chain/contracts/DreggSettlement.sol` -- the
//! OUTBOUND settlement leg for $DREGG's home chain. It verifies the SAME BN254
//! dregg Groth16 proof the EVM `DreggGroth16Verifier25` checks (the 25-lane
//! whole-history statement, `circuit-prove/src/ivc_turn_chain.rs`), on-chain, via
//! the Solana `alt_bn128` syscalls, and advances a proven root.
//!
//! ## What it gives Solana
//!
//! Before this program, the Solana side of the mirror was purely off-chain: the
//! `bridge/src/solana_relayer.rs` watcher + the oracle-attested lock
//! (`solana-lock/`). There was no ON-CHAIN verification that a dregg state
//! transition actually happened. This program is that verification -- the twin of
//! the EVM settlement, giving Solana OUTBOUND parity with EVM: a dregg proof
//! verified on-chain, fail-closed, on the home chain.
//!
//! ## The proof
//!
//! A gnark Groth16(BN254) with a Pedersen commitment (the wrap circuit's
//! commit-based range checker). [`groth16::verify`] reproduces
//! `DreggGroth16Verifier25.verifyProof` bit-for-bit: the commitment
//! proof-of-knowledge pairing, the keccak commitment-hash input, the public-input
//! MSM, and the 4-pair Groth16 pairing -- all on the `alt_bn128` syscalls
//! (`solana_bn254::prelude`, which is the syscall on-chain and the identical
//! ark-bn254 arithmetic in host tests).
//!
//! ## The VK
//!
//! [`vk`] is GENERATED from the deployed EVM verifier's embedded constants
//! (`scripts/gen_vk.py`) -- the SAME gnark verifying key, re-encoded for the
//! Solana syscalls. The proof is chain-agnostic BN254; only the on-chain verifier
//! differs. The pinned `vk_hash` (`keccak256("dregg-settlement-vk-dev-setup")`)
//! and genesis anchor are byte-identical to the live Base-Sepolia deployment
//! (`chain/DEPLOYMENTS.md`), a dev-ceremony key -- NOT a production MPC setup.

pub mod error;
pub mod groth16;
pub mod instruction;
pub mod processor;
pub mod state;
pub mod vk;

use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult, pubkey::Pubkey};

/// PDA seed for the singleton settlement state account.
pub const SEED_SETTLEMENT: &[u8] = b"settlement";

/// The dev-ceremony verifying-key hash pinned by the live EVM deployment
/// (`chain/script/DeploySettlement.s.sol`: `keccak256("dregg-settlement-vk-dev-setup")`).
/// A settlement init pins THIS on the Solana side too, so the on-chain VK
/// commitment is byte-identical across chains. A dev single-party setup
/// (toxic-waste-known), NOT a production MPC ceremony.
pub fn dev_ceremony_vk_hash() -> [u8; 32] {
    solana_program::keccak::hashv(&[b"dregg-settlement-vk-dev-setup"]).0
}

// Native entrypoint. Gated so `cargo test` (host) and dependents can link the
// library without a second `entrypoint` symbol.
#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_instruction);

/// Dispatch on the 1-byte tag. All real logic lives in [`processor`].
pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    processor::process(program_id, accounts, instruction_data)
}
