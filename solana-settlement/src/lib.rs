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
//! [`vk`] is GENERATED from the canonical spec `chain/codegen/dregg_vk.json` by
//! `chain/codegen/gen_verifiers.py` -- the SAME gnark verifying key the EVM
//! `DreggGroth16Verifier25` embeds, re-encoded for the Solana syscalls. The proof
//! is chain-agnostic BN254; only the on-chain verifier differs. The key is a dev
//! single-party ceremony (toxic-waste-known), NOT a production MPC setup.
//!
//! The pinned `vk_hash` is [`settlement_vk_digest`] = [`vk::VK_DIGEST`], keccak256
//! over the canonical serialization of THAT key (see [`vk_digest`]), byte-identical
//! on EVM (`DreggSettlementVK.VK_DIGEST`) and Cosmos. It replaced
//! `keccak256("dregg-settlement-vk-dev-setup")` on 2026-07-28: that pin was a hash
//! of a LABEL and so was byte-identical under every regeneration of the key.

pub mod error;
pub mod groth16;
pub mod instruction;
pub mod merkle;
pub mod processor;
pub mod state;
pub mod vk;
pub mod vk_digest;

use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult, pubkey::Pubkey};

/// PDA seed for the singleton settlement state account.
pub const SEED_SETTLEMENT: &[u8] = b"settlement";

/// PDA seed prefix for a per-root registry marker (`isProvenRoot`). The full
/// seeds are `[SEED_PROVEN_ROOT, packLanes(root)]`; the marker's existence
/// (program-owned) is the on-chain proof that a settlement recorded that root.
pub const SEED_PROVEN_ROOT: &[u8] = b"proven_root";

/// THE verifying-key commitment this program pins: keccak256 over the canonical
/// serialization of the verifying key in [`vk`] (see [`vk_digest`] for the exact
/// preimage). `InitSettlement` REFUSES any other value, so a settlement account
/// can only ever be pinned to the key the program actually verifies against.
///
/// Byte-identical to `DreggSettlementVK.VK_DIGEST` (EVM) and
/// `cosmos_settlement::vk::VK_DIGEST` -- all three emitted from
/// `chain/codegen/dregg_vk.json` -- so cross-chain pin equality now means "the
/// same key", which under the previous label hash it did not.
///
/// ⚠ FLAG DAY 2026-07-28: this replaced `dev_ceremony_vk_hash()` =
/// `keccak256("dregg-settlement-vk-dev-setup")` =
/// `0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76`. Any
/// settlement account initialized before that pins the old value and must be
/// re-initialized; every deploy script and test that hard-coded the label hash
/// now refuses (`SettlementError::VkDigestMismatch`).
pub fn settlement_vk_digest() -> [u8; 32] {
    vk::VK_DIGEST
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
