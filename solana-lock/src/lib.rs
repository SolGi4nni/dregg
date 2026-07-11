//! # dregg Solana lock program (native, no Anchor)
//!
//! The Solana SIDE of the dregg token mirror (`docs/deos/TOKEN-MIRROR-BRIDGE.md`,
//! the "named, not built" gap). A `$DREGG` holder calls [`instruction::LockInstruction::Lock`]
//! to escrow their SPL `$DREGG` into a program-owned vault; the program writes a
//! 72-byte lock record the dregg relayer decodes and mirrors into the shielded
//! value layer.
//!
//! ## Why the layout is load-bearing
//!
//! The dregg relayer reads a lock-record account and (a) REQUIRES its Solana-owner
//! == the configured `lock_program` (this program), (b) decodes exactly 72 bytes
//! `lock_id(32) ‖ recipient(32) ‖ amount_le(8)` via `decode_lock_record`
//! (`bridge/src/solana_wire.rs:614-644`), (c) binds mint/amount/vault
//! (`bridge/src/solana_relayer.rs:671-738`, `observe_lock_at` /
//! `verify_finalized_account`; `scan_program_locks` iterates all accounts THIS
//! program owns). So the program MUST own every lock-record account and write those
//! exact 72 bytes — see [`record`].
//!
//! ## lock_id derivation
//!
//! `lock_id` (the mirror's replay nonce; `bridge/src/solana_mirror.rs:94-98`) is the
//! **32-byte pubkey of the per-lock record PDA** itself. That PDA is derived from
//! `[b"lock", config, nonce_le]` where `nonce` is a monotonic counter in the config
//! account, so every lock gets a globally-unique, deterministic `lock_id` with no
//! extra account. (The mirror computes `nullifier = H(spl_mint, lock_id)`; a unique
//! `lock_id` ⇒ a unique consume-once nullifier.)
//!
//! ## Trust residual (unlock)
//!
//! [`instruction::LockInstruction::Unlock`] models the redeem path: it checks a
//! configured ed25519 `unlock_authority` signature + a redeem-receipt-PDA anti-replay,
//! then CPI-transfers `$DREGG` out. A real deployment gates this on *verifying a
//! dregg burn/unlock attestation* on-chain (a threshold-sig check over the
//! `SolanaUnlockRequest`); that verification is the named residual — see the module
//! `unlock` note in [`processor`].

pub mod error;
pub mod instruction;
pub mod record;
pub mod state;

pub mod processor;

use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult, pubkey::Pubkey};

// PDA seed prefixes (documented above).
pub const SEED_CONFIG: &[u8] = b"config";
pub const SEED_VAULT: &[u8] = b"vault";
pub const SEED_VAULT_AUTHORITY: &[u8] = b"vault_authority";
pub const SEED_LOCK: &[u8] = b"lock";
pub const SEED_REDEEM: &[u8] = b"redeem";

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
