//! The instruction processor: PDA derivation, CPI, and fail-closed checks.

use solana_program::{
    account_info::{next_account_info, AccountInfo},
    clock::Clock,
    ed25519_program,
    entrypoint::ProgramResult,
    msg,
    program::{invoke, invoke_signed},
    program_error::ProgramError,
    program_pack::Pack,
    pubkey::Pubkey,
    rent::Rent,
    system_instruction,
    sysvar::Sysvar,
};

use solana_instructions_sysvar::{self as instructions_sysvar};

use crate::attestation::{parse_ed25519_refs, unlock_message_hash, PUBKEY_SERIALIZED_SIZE};
use crate::error::LockError;
use crate::escrow::{EscrowRecord, EscrowStatus, ESCROW_RECORD_LEN};
use crate::instruction::LockInstruction;
use crate::record::{encode_lock_record, LOCK_RECORD_LEN};
use crate::state::{VaultConfig, CONFIG_LEN, MAX_ORACLE_KEYS};
use crate::{
    SEED_CONFIG, SEED_ESCROW, SEED_ESCROW_AUTHORITY, SEED_ESCROW_VAULT, SEED_LOCK, SEED_REDEEM,
    SEED_VAULT, SEED_VAULT_AUTHORITY,
};

/// Upper bound on how many transaction instructions we will scan for oracle
/// signatures. Solana caps instructions per transaction well below this; the bound
/// only guards against an unbounded loop.
const MAX_TX_INSTRUCTIONS: usize = 128;

pub fn process(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    match LockInstruction::unpack(instruction_data)? {
        LockInstruction::InitVault {
            oracle_threshold,
            oracle_keys,
        } => init_vault(program_id, accounts, oracle_threshold, oracle_keys),
        LockInstruction::Lock {
            amount,
            dregg_recipient,
        } => lock(program_id, accounts, amount, dregg_recipient),
        LockInstruction::Unlock { amount, redeem_id } => {
            unlock(program_id, accounts, amount, redeem_id)
        }
        LockInstruction::EscrowLock {
            amount,
            deadline,
            escrow_id,
        } => escrow_lock(program_id, accounts, amount, deadline, escrow_id),
        LockInstruction::EscrowRelease { amount, escrow_id } => {
            escrow_release(program_id, accounts, amount, escrow_id)
        }
        LockInstruction::EscrowRefund { escrow_id } => {
            escrow_refund(program_id, accounts, escrow_id)
        }
    }
}

/// Derive the per-config escrow custody authority PDA (`[b"escrow_authority",
/// config]`) — the SPL owner of every per-escrow vault token account.
fn escrow_authority_pda(program_id: &Pubkey, config: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[SEED_ESCROW_AUTHORITY, config.as_ref()], program_id)
}

/// Derive the config PDA and assert the passed account matches it.
fn expect_config_pda(program_id: &Pubkey, key: &Pubkey) -> Result<u8, LockError> {
    let (pda, bump) = Pubkey::find_program_address(&[SEED_CONFIG], program_id);
    if &pda != key {
        return Err(LockError::InvalidPda);
    }
    Ok(bump)
}

fn vault_authority_pda(program_id: &Pubkey, config: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[SEED_VAULT_AUTHORITY, config.as_ref()], program_id)
}

// ---------------------------------------------------------------------------
// InitVault
// ---------------------------------------------------------------------------

/// Accounts (in order):
///   0. `[signer, writable]` payer (funds the created accounts)
///   1. `[writable]`         config PDA `[b"config"]` (created, program-owned)
///   2. `[]`                 the $DREGG SPL mint
///   3. `[writable]`         vault token account PDA `[b"vault", config]` (created + SPL-init)
///   4. `[]`                 vault authority PDA `[b"vault_authority", config]` (SPL owner of the vault)
///   5. `[]`                 SPL Token program
///   6. `[]`                 System program
///
/// `oracle_threshold` (M) and `oracle_keys` (N) define the M-of-N ed25519 oracle
/// set that authorizes an [`LockInstruction::Unlock`]. Fail-closed: the set is
/// validated (`1 <= M <= N <= MAX_ORACLE_KEYS`, no zero key, no duplicate) before
/// the config is written.
fn init_vault(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    oracle_threshold: u8,
    oracle_keys: Vec<[u8; 32]>,
) -> ProgramResult {
    let ai = &mut accounts.iter();
    let payer = next_account_info(ai)?;
    let config_ai = next_account_info(ai)?;
    let mint_ai = next_account_info(ai)?;
    let vault_ai = next_account_info(ai)?;
    let vault_authority_ai = next_account_info(ai)?;
    let token_program = next_account_info(ai)?;
    let system_program = next_account_info(ai)?;

    if !payer.is_signer {
        return Err(LockError::MissingSigner.into());
    }

    let config_bump = expect_config_pda(program_id, config_ai.key)?;

    // Fresh init only: the config PDA must not already be a program-owned config.
    if !config_ai.data_is_empty() {
        return Err(LockError::AccountState.into());
    }

    // vault token account PDA + vault authority PDA
    let (vault_pda, vault_bump) =
        Pubkey::find_program_address(&[SEED_VAULT, config_ai.key.as_ref()], program_id);
    if &vault_pda != vault_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    let (vault_auth_pda, vault_auth_bump) = vault_authority_pda(program_id, config_ai.key);
    if &vault_auth_pda != vault_authority_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    if token_program.key != &spl_token::id() {
        return Err(LockError::AccountMismatch.into());
    }

    let rent = Rent::get()?;

    // (1) create the program-owned config account.
    create_pda_account(
        payer,
        config_ai,
        system_program,
        program_id,
        CONFIG_LEN,
        &[SEED_CONFIG, &[config_bump]],
        &rent,
    )?;

    // (2) create the SPL token vault account (owned by the SPL Token program).
    create_pda_account(
        payer,
        vault_ai,
        system_program,
        &spl_token::id(),
        spl_token::state::Account::LEN,
        &[SEED_VAULT, config_ai.key.as_ref(), &[vault_bump]],
        &rent,
    )?;

    // (3) initialize the vault token account with authority = vault-authority PDA.
    let init_ix = spl_token::instruction::initialize_account3(
        &spl_token::id(),
        vault_ai.key,
        mint_ai.key,
        vault_authority_ai.key,
    )?;
    invoke(
        &init_ix,
        &[vault_ai.clone(), mint_ai.clone(), token_program.clone()],
    )?;

    // (4) build + validate the oracle set, then write the config. `pack_into`
    //     re-validates, so a malformed set (empty, M=0, M>N, zero key, duplicate)
    //     can never be persisted.
    let count = oracle_keys.len();
    if count == 0 || count > MAX_ORACLE_KEYS {
        return Err(LockError::InvalidOracleSet.into());
    }
    let mut keys = [[0u8; 32]; MAX_ORACLE_KEYS];
    for (slot, k) in keys.iter_mut().zip(oracle_keys.iter()) {
        *slot = *k;
    }
    let cfg = VaultConfig {
        mint: mint_ai.key.to_bytes(),
        vault_token_account: vault_ai.key.to_bytes(),
        vault_authority_bump: vault_auth_bump,
        nonce: 0,
        oracle_threshold,
        oracle_count: count as u8,
        oracle_keys: keys,
    };
    cfg.validate_oracle_set()?;
    cfg.pack_into(&mut config_ai.try_borrow_mut_data()?)?;
    msg!(
        "dregg-lock: vault initialized for mint {} ({}-of-{} oracle set)",
        mint_ai.key,
        oracle_threshold,
        count
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// Lock — THE mint path
// ---------------------------------------------------------------------------

/// Accounts (in order):
///   0. `[signer, writable]` payer (funds the lock-record account)
///   1. `[writable]`         config PDA `[b"config"]`
///   2. `[writable]`         user's $DREGG token account (source)
///   3. `[writable]`         vault token account (dest; must == config.vault_token_account)
///   4. `[signer]`           user authority (SPL owner of the source account)
///   5. `[writable]`         lock-record PDA `[b"lock", config, nonce_le]` (created, program-owned, 72 bytes)
///   6. `[]`                 SPL Token program
///   7. `[]`                 System program
fn lock(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    amount: u64,
    dregg_recipient: [u8; 32],
) -> ProgramResult {
    if amount == 0 {
        return Err(LockError::ZeroAmount.into());
    }

    let ai = &mut accounts.iter();
    let payer = next_account_info(ai)?;
    let config_ai = next_account_info(ai)?;
    let user_token_ai = next_account_info(ai)?;
    let vault_ai = next_account_info(ai)?;
    let user_authority = next_account_info(ai)?;
    let record_ai = next_account_info(ai)?;
    let token_program = next_account_info(ai)?;
    let system_program = next_account_info(ai)?;

    if !payer.is_signer {
        return Err(LockError::MissingSigner.into());
    }
    if !user_authority.is_signer {
        return Err(LockError::MissingSigner.into());
    }
    expect_config_pda(program_id, config_ai.key)?;

    // config must be a program-owned, valid config.
    if config_ai.owner != program_id {
        return Err(LockError::WrongOwner.into());
    }
    let mut cfg = VaultConfig::unpack(&config_ai.try_borrow_data()?)?;

    if token_program.key != &spl_token::id() {
        return Err(LockError::AccountMismatch.into());
    }
    // the destination MUST be the configured vault token account.
    if vault_ai.key.to_bytes() != cfg.vault_token_account {
        return Err(LockError::MintMismatch.into());
    }

    // derive THIS lock's record PDA from the current nonce.
    let nonce = cfg.nonce;
    let (record_pda, record_bump) = Pubkey::find_program_address(
        &[SEED_LOCK, config_ai.key.as_ref(), &nonce.to_le_bytes()],
        program_id,
    );
    if &record_pda != record_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    if !record_ai.data_is_empty() {
        // nonce collision / already used — fail closed.
        return Err(LockError::AccountState.into());
    }

    // (1) CPI: transfer `amount` $DREGG from the user into the vault. The SPL Token
    //     program enforces source.mint == dest.mint and that `user_authority` owns
    //     the source; a wrong mint or unauthorized source aborts the whole tx.
    let transfer_ix = spl_token::instruction::transfer(
        &spl_token::id(),
        user_token_ai.key,
        vault_ai.key,
        user_authority.key,
        &[],
        amount,
    )?;
    invoke(
        &transfer_ix,
        &[
            user_token_ai.clone(),
            vault_ai.clone(),
            user_authority.clone(),
            token_program.clone(),
        ],
    )?;

    // (2) create the program-owned 72-byte lock-record account.
    let rent = Rent::get()?;
    create_pda_account(
        payer,
        record_ai,
        system_program,
        program_id,
        LOCK_RECORD_LEN,
        &[
            SEED_LOCK,
            config_ai.key.as_ref(),
            &nonce.to_le_bytes(),
            &[record_bump],
        ],
        &rent,
    )?;

    // (3) write the record. lock_id = the record PDA's own pubkey (unique per nonce).
    //     Layout: lock_id(32) ‖ recipient(32) ‖ amount_le(8) — bridge/src/solana_wire.rs:614-644.
    let lock_id = record_ai.key.to_bytes();
    let data = encode_lock_record(&lock_id, &dregg_recipient, amount);
    record_ai.try_borrow_mut_data()?.copy_from_slice(&data);

    // (4) bump the nonce so the next lock gets a fresh unique record PDA / lock_id.
    cfg.nonce = cfg.nonce.checked_add(1).ok_or(LockError::AccountState)?;
    cfg.pack_into(&mut config_ai.try_borrow_mut_data()?)?;

    msg!(
        "dregg-lock: locked {} for recipient, lock_id = record pda {}",
        amount,
        record_ai.key
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// Unlock — the redeem path
// ---------------------------------------------------------------------------

/// Accounts (in order):
///   0. `[]`                 config PDA `[b"config"]`
///   1. `[writable]`         vault token account (source; must == config.vault_token_account)
///   2. `[]`                 vault authority PDA `[b"vault_authority", config]` (signs the transfer out)
///   3. `[writable]`         recipient $DREGG token account (dest; also the attested `solana_recipient`)
///   4. `[writable]`         redeem-receipt PDA `[b"redeem", config, redeem_id]` (created; anti-replay)
///   5. `[signer, writable]` payer (funds the redeem receipt)
///   6. `[]`                 SPL Token program
///   7. `[]`                 System program
///   8. `[]`                 instructions sysvar (`Sysvar1nstructions1111111111111111111111111`)
///
/// TRUST BOUNDARY — this VERIFIES a dregg unlock attestation on-chain: it
/// reconstructs the canonical [`unlock_message_hash`] of
/// `SolanaUnlockRequest { spl_mint = config.mint, amount, solana_recipient =
/// recipient token account, redeem_id }` and requires `>= M` valid ed25519
/// signatures from DISTINCT configured oracle keys over that hash. The signatures
/// ride in ed25519 native-program (precompile) instructions in the same
/// transaction; the runtime verifies them before this executes, and we resolve
/// exactly the (pubkey, message) pairs it verified via the instructions sysvar.
fn unlock(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    amount: u64,
    redeem_id: [u8; 32],
) -> ProgramResult {
    if amount == 0 {
        return Err(LockError::ZeroAmount.into());
    }

    let ai = &mut accounts.iter();
    let config_ai = next_account_info(ai)?;
    let vault_ai = next_account_info(ai)?;
    let vault_authority_ai = next_account_info(ai)?;
    let recipient_ai = next_account_info(ai)?;
    let receipt_ai = next_account_info(ai)?;
    let payer = next_account_info(ai)?;
    let token_program = next_account_info(ai)?;
    let system_program = next_account_info(ai)?;
    let instructions_ai = next_account_info(ai)?;

    expect_config_pda(program_id, config_ai.key)?;
    if config_ai.owner != program_id {
        return Err(LockError::WrongOwner.into());
    }
    // unpack re-enforces the NOMAD-LAW invariants (1 <= M <= N, no empty set).
    let cfg = VaultConfig::unpack(&config_ai.try_borrow_data()?)?;

    if !payer.is_signer {
        return Err(LockError::MissingSigner.into());
    }
    if token_program.key != &spl_token::id() {
        return Err(LockError::AccountMismatch.into());
    }
    if vault_ai.key.to_bytes() != cfg.vault_token_account {
        return Err(LockError::MintMismatch.into());
    }

    // vault authority PDA (signs transfer out of the vault).
    let (vault_auth_pda, vault_auth_bump) = vault_authority_pda(program_id, config_ai.key);
    if &vault_auth_pda != vault_authority_ai.key || vault_auth_bump != cfg.vault_authority_bump {
        return Err(LockError::InvalidPda.into());
    }

    // -----------------------------------------------------------------------
    // THE trust check: verify an M-of-N ed25519 threshold attestation over the
    // canonical unlock message hash. NOMAD-LAW: a config with M=0 or an empty
    // key-set cannot even be loaded (unpack rejects it), and below we require
    // `distinct_signers >= M` with M >= 1 — so zero/empty signatures never pass.
    // -----------------------------------------------------------------------
    let solana_recipient = recipient_ai.key.to_bytes();
    let message_hash = unlock_message_hash(&cfg.mint, amount, &solana_recipient, &redeem_id);

    // Defensive belt-and-suspenders against a future path that could load an
    // invalid config: an unlock is impossible without a positive threshold.
    if cfg.oracle_threshold == 0 {
        return Err(LockError::ThresholdNotMet.into());
    }
    let distinct = count_oracle_signers(instructions_ai, &cfg, &message_hash)?;
    if distinct < cfg.oracle_threshold as usize {
        msg!(
            "dregg-lock: unlock refused — {} distinct oracle sigs < threshold {}",
            distinct,
            cfg.oracle_threshold
        );
        return Err(LockError::ThresholdNotMet.into());
    }

    // anti-replay: the redeem-receipt PDA for this redeem_id must not exist yet.
    let (receipt_pda, receipt_bump) = Pubkey::find_program_address(
        &[SEED_REDEEM, config_ai.key.as_ref(), &redeem_id],
        program_id,
    );
    if &receipt_pda != receipt_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    if !receipt_ai.data_is_empty() || receipt_ai.lamports() > 0 {
        return Err(LockError::AlreadyRedeemed.into());
    }

    // (1) create the redeem receipt FIRST (mark consumed) — fail-closed against a
    //     re-entrant / duplicated redeem in the same slot.
    let rent = Rent::get()?;
    create_pda_account(
        payer,
        receipt_ai,
        system_program,
        program_id,
        1,
        &[
            SEED_REDEEM,
            config_ai.key.as_ref(),
            &redeem_id,
            &[receipt_bump],
        ],
        &rent,
    )?;
    receipt_ai.try_borrow_mut_data()?[0] = 1;

    // (2) CPI: transfer `amount` $DREGG out of the vault to the recipient, signed by
    //     the vault-authority PDA.
    let transfer_ix = spl_token::instruction::transfer(
        &spl_token::id(),
        vault_ai.key,
        recipient_ai.key,
        vault_authority_ai.key,
        &[],
        amount,
    )?;
    invoke_signed(
        &transfer_ix,
        &[
            vault_ai.clone(),
            recipient_ai.clone(),
            vault_authority_ai.clone(),
            token_program.clone(),
        ],
        &[&[
            SEED_VAULT_AUTHORITY,
            config_ai.key.as_ref(),
            &[vault_auth_bump],
        ]],
    )?;

    msg!("dregg-lock: unlocked {} (redeem_id consumed)", amount);
    Ok(())
}

// ---------------------------------------------------------------------------
// Escrow (timeout/refund) — the two-branch, exactly-once DrEX routing-safety twin
// ---------------------------------------------------------------------------

/// ESCROW LOCK — escrow `amount` of $DREGG into a per-escrow vault under `escrow_id`,
/// reclaimable after `deadline` if no DrEX fill clears it.
///
/// Accounts (in order):
///   0. `[signer, writable]` payer (funds the escrow vault + record accounts)
///   1. `[]`                 config PDA `[b"config"]` (for the mint)
///   2. `[writable]`         user's $DREGG token account (source AND refund destination)
///   3. `[writable]`         per-escrow vault token account `[b"escrow_vault", config, escrow_id]` (created + SPL-init)
///   4. `[]`                 escrow authority PDA `[b"escrow_authority", config]` (SPL owner of the escrow vault)
///   5. `[signer]`           user authority (SPL owner of the source; the depositor / sole refunder)
///   6. `[writable]`         escrow record PDA `[b"escrow", config, escrow_id]` (created, program-owned)
///   7. `[]`                 the $DREGG SPL mint
///   8. `[]`                 SPL Token program
///   9. `[]`                 System program
fn escrow_lock(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    amount: u64,
    deadline: i64,
    escrow_id: [u8; 32],
) -> ProgramResult {
    if amount == 0 {
        return Err(LockError::ZeroAmount.into());
    }
    // Fail-closed: a non-positive deadline would make refund immediately available,
    // defeating the timed lock (and could underflow the "> deadline" intent).
    if deadline <= 0 {
        return Err(LockError::ZeroDeadline.into());
    }

    let ai = &mut accounts.iter();
    let payer = next_account_info(ai)?;
    let config_ai = next_account_info(ai)?;
    let user_token_ai = next_account_info(ai)?;
    let escrow_vault_ai = next_account_info(ai)?;
    let escrow_authority_ai = next_account_info(ai)?;
    let user_authority = next_account_info(ai)?;
    let record_ai = next_account_info(ai)?;
    let mint_ai = next_account_info(ai)?;
    let token_program = next_account_info(ai)?;
    let system_program = next_account_info(ai)?;

    if !payer.is_signer {
        return Err(LockError::MissingSigner.into());
    }
    if !user_authority.is_signer {
        return Err(LockError::MissingSigner.into());
    }
    expect_config_pda(program_id, config_ai.key)?;
    if config_ai.owner != program_id {
        return Err(LockError::WrongOwner.into());
    }
    let cfg = VaultConfig::unpack(&config_ai.try_borrow_data()?)?;
    if token_program.key != &spl_token::id() {
        return Err(LockError::AccountMismatch.into());
    }
    if mint_ai.key.to_bytes() != cfg.mint {
        return Err(LockError::MintMismatch.into());
    }

    // Escrow authority PDA (SPL owner of the per-escrow vault).
    let (escrow_auth_pda, _escrow_auth_bump) = escrow_authority_pda(program_id, config_ai.key);
    if &escrow_auth_pda != escrow_authority_ai.key {
        return Err(LockError::InvalidPda.into());
    }

    // Per-escrow vault token account PDA.
    let (vault_pda, vault_bump) = Pubkey::find_program_address(
        &[SEED_ESCROW_VAULT, config_ai.key.as_ref(), &escrow_id],
        program_id,
    );
    if &vault_pda != escrow_vault_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    // Per-escrow record PDA. Freshness of THIS account is the exactly-once id guard:
    // a terminal escrow keeps its record, so an escrow_id can never be relocked.
    let (record_pda, record_bump) = Pubkey::find_program_address(
        &[SEED_ESCROW, config_ai.key.as_ref(), &escrow_id],
        program_id,
    );
    if &record_pda != record_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    if !record_ai.data_is_empty() || !escrow_vault_ai.data_is_empty() {
        return Err(LockError::AccountState.into());
    }

    let rent = Rent::get()?;

    // (1) create + SPL-init the per-escrow vault token account (authority = escrow authority PDA).
    create_pda_account(
        payer,
        escrow_vault_ai,
        system_program,
        &spl_token::id(),
        spl_token::state::Account::LEN,
        &[
            SEED_ESCROW_VAULT,
            config_ai.key.as_ref(),
            &escrow_id,
            &[vault_bump],
        ],
        &rent,
    )?;
    let init_ix = spl_token::instruction::initialize_account3(
        &spl_token::id(),
        escrow_vault_ai.key,
        mint_ai.key,
        escrow_authority_ai.key,
    )?;
    invoke(
        &init_ix,
        &[
            escrow_vault_ai.clone(),
            mint_ai.clone(),
            token_program.clone(),
        ],
    )?;

    // (2) CPI: transfer `amount` from the user into the per-escrow vault.
    let transfer_ix = spl_token::instruction::transfer(
        &spl_token::id(),
        user_token_ai.key,
        escrow_vault_ai.key,
        user_authority.key,
        &[],
        amount,
    )?;
    invoke(
        &transfer_ix,
        &[
            user_token_ai.clone(),
            escrow_vault_ai.clone(),
            user_authority.clone(),
            token_program.clone(),
        ],
    )?;

    // (3) create + write the program-owned escrow record (status = Locked).
    create_pda_account(
        payer,
        record_ai,
        system_program,
        program_id,
        ESCROW_RECORD_LEN,
        &[
            SEED_ESCROW,
            config_ai.key.as_ref(),
            &escrow_id,
            &[record_bump],
        ],
        &rent,
    )?;
    let rec = EscrowRecord {
        status: EscrowStatus::Locked,
        mint: cfg.mint,
        depositor: user_authority.key.to_bytes(),
        refund_destination: user_token_ai.key.to_bytes(),
        amount,
        deadline,
        escrow_id,
    };
    rec.pack_into(&mut record_ai.try_borrow_mut_data()?)?;

    msg!(
        "dregg-lock: escrow locked {} (deadline {})",
        amount,
        deadline
    );
    Ok(())
}

/// ESCROW RELEASE — pay a locked escrow to the ring-matched recipient, authorized by
/// an M-of-N ed25519 oracle attestation over `unlock_message_hash(mint, amount,
/// recipient, escrow_id)` (the Solana AssertProvenRoot analog). Terminal: `Released`.
///
/// Accounts (in order):
///   0. `[]`                 config PDA `[b"config"]` (oracle set + mint)
///   1. `[writable]`         escrow record PDA `[b"escrow", config, escrow_id]`
///   2. `[writable]`         per-escrow vault token account (source)
///   3. `[]`                 escrow authority PDA `[b"escrow_authority", config]` (signs transfer out)
///   4. `[writable]`         recipient $DREGG token account (dest; the attested `solana_recipient`)
///   5. `[]`                 SPL Token program
///   6. `[]`                 instructions sysvar
fn escrow_release(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    amount: u64,
    escrow_id: [u8; 32],
) -> ProgramResult {
    if amount == 0 {
        return Err(LockError::ZeroAmount.into());
    }

    let ai = &mut accounts.iter();
    let config_ai = next_account_info(ai)?;
    let record_ai = next_account_info(ai)?;
    let escrow_vault_ai = next_account_info(ai)?;
    let escrow_authority_ai = next_account_info(ai)?;
    let recipient_ai = next_account_info(ai)?;
    let token_program = next_account_info(ai)?;
    let instructions_ai = next_account_info(ai)?;

    expect_config_pda(program_id, config_ai.key)?;
    if config_ai.owner != program_id {
        return Err(LockError::WrongOwner.into());
    }
    let cfg = VaultConfig::unpack(&config_ai.try_borrow_data()?)?;
    if token_program.key != &spl_token::id() {
        return Err(LockError::AccountMismatch.into());
    }

    // Record PDA + program ownership.
    let (record_pda, _record_bump) = Pubkey::find_program_address(
        &[SEED_ESCROW, config_ai.key.as_ref(), &escrow_id],
        program_id,
    );
    if &record_pda != record_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    if record_ai.owner != program_id {
        return Err(LockError::WrongOwner.into());
    }
    let mut rec = EscrowRecord::unpack(&record_ai.try_borrow_data()?)?;

    // EXACTLY-ONCE: only a Locked escrow can transition; a terminal one is refused.
    if rec.status != EscrowStatus::Locked {
        return Err(LockError::EscrowNotLocked.into());
    }
    if rec.escrow_id != escrow_id || rec.mint != cfg.mint || rec.amount != amount {
        return Err(LockError::EscrowFieldMismatch.into());
    }

    // Per-escrow vault PDA.
    let (vault_pda, _vault_bump) = Pubkey::find_program_address(
        &[SEED_ESCROW_VAULT, config_ai.key.as_ref(), &escrow_id],
        program_id,
    );
    if &vault_pda != escrow_vault_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    let (escrow_auth_pda, escrow_auth_bump) = escrow_authority_pda(program_id, config_ai.key);
    if &escrow_auth_pda != escrow_authority_ai.key {
        return Err(LockError::InvalidPda.into());
    }

    // THE trust check: M-of-N oracle attestation over the canonical unlock hash,
    // binding the recipient token account + escrow_id (escrow_id doubles as the
    // attestation redeem/nonce). Reuses the exact verification path as `unlock`.
    let solana_recipient = recipient_ai.key.to_bytes();
    let message_hash = unlock_message_hash(&cfg.mint, amount, &solana_recipient, &escrow_id);
    if cfg.oracle_threshold == 0 {
        return Err(LockError::ThresholdNotMet.into());
    }
    let distinct = count_oracle_signers(instructions_ai, &cfg, &message_hash)?;
    if distinct < cfg.oracle_threshold as usize {
        msg!(
            "dregg-lock: escrow release refused — {} distinct oracle sigs < threshold {}",
            distinct,
            cfg.oracle_threshold
        );
        return Err(LockError::ThresholdNotMet.into());
    }

    // Effects BEFORE interaction: consume the lock (terminal Released).
    rec.status = EscrowStatus::Released;
    rec.pack_into(&mut record_ai.try_borrow_mut_data()?)?;

    // Transfer the escrowed amount to the recipient, signed by the escrow authority.
    let transfer_ix = spl_token::instruction::transfer(
        &spl_token::id(),
        escrow_vault_ai.key,
        recipient_ai.key,
        escrow_authority_ai.key,
        &[],
        amount,
    )?;
    invoke_signed(
        &transfer_ix,
        &[
            escrow_vault_ai.clone(),
            recipient_ai.clone(),
            escrow_authority_ai.clone(),
            token_program.clone(),
        ],
        &[&[
            SEED_ESCROW_AUTHORITY,
            config_ai.key.as_ref(),
            &[escrow_auth_bump],
        ]],
    )?;

    msg!("dregg-lock: escrow released {}", amount);
    Ok(())
}

/// ESCROW REFUND — after the deadline, the depositor reclaims a locked escrow to its
/// captured refund destination. No attestation (the timeout IS the condition).
/// Terminal: `Refunded`.
///
/// Accounts (in order):
///   0. `[]`                 config PDA `[b"config"]`
///   1. `[writable]`         escrow record PDA `[b"escrow", config, escrow_id]`
///   2. `[writable]`         per-escrow vault token account (source)
///   3. `[]`                 escrow authority PDA `[b"escrow_authority", config]` (signs transfer out)
///   4. `[writable]`         refund destination token account (must == record.refund_destination)
///   5. `[signer]`           depositor authority (must == record.depositor)
///   6. `[]`                 SPL Token program
fn escrow_refund(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    escrow_id: [u8; 32],
) -> ProgramResult {
    let ai = &mut accounts.iter();
    let config_ai = next_account_info(ai)?;
    let record_ai = next_account_info(ai)?;
    let escrow_vault_ai = next_account_info(ai)?;
    let escrow_authority_ai = next_account_info(ai)?;
    let refund_dest_ai = next_account_info(ai)?;
    let depositor_authority = next_account_info(ai)?;
    let token_program = next_account_info(ai)?;

    expect_config_pda(program_id, config_ai.key)?;
    if config_ai.owner != program_id {
        return Err(LockError::WrongOwner.into());
    }
    if token_program.key != &spl_token::id() {
        return Err(LockError::AccountMismatch.into());
    }

    // Record PDA + program ownership + Locked status.
    let (record_pda, _record_bump) = Pubkey::find_program_address(
        &[SEED_ESCROW, config_ai.key.as_ref(), &escrow_id],
        program_id,
    );
    if &record_pda != record_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    if record_ai.owner != program_id {
        return Err(LockError::WrongOwner.into());
    }
    let mut rec = EscrowRecord::unpack(&record_ai.try_borrow_data()?)?;
    if rec.status != EscrowStatus::Locked {
        return Err(LockError::EscrowNotLocked.into());
    }
    if rec.escrow_id != escrow_id {
        return Err(LockError::EscrowFieldMismatch.into());
    }

    // THE refund condition: the deadline must have STRICTLY passed. A release wins
    // over a timeout only while Locked (checked above); here the timeout is the sole
    // authorization — no attestation.
    let now = Clock::get()?.unix_timestamp;
    if now <= rec.deadline {
        return Err(LockError::RefundBeforeDeadline.into());
    }

    // Only the recorded depositor may refund, and only to the captured destination.
    if !depositor_authority.is_signer {
        return Err(LockError::MissingSigner.into());
    }
    if depositor_authority.key.to_bytes() != rec.depositor {
        return Err(LockError::EscrowFieldMismatch.into());
    }
    if refund_dest_ai.key.to_bytes() != rec.refund_destination {
        return Err(LockError::EscrowFieldMismatch.into());
    }

    // Per-escrow vault PDA + authority PDA.
    let (vault_pda, _vault_bump) = Pubkey::find_program_address(
        &[SEED_ESCROW_VAULT, config_ai.key.as_ref(), &escrow_id],
        program_id,
    );
    if &vault_pda != escrow_vault_ai.key {
        return Err(LockError::InvalidPda.into());
    }
    let (escrow_auth_pda, escrow_auth_bump) = escrow_authority_pda(program_id, config_ai.key);
    if &escrow_auth_pda != escrow_authority_ai.key {
        return Err(LockError::InvalidPda.into());
    }

    // Effects BEFORE interaction: consume the lock (terminal Refunded).
    let amount = rec.amount;
    rec.status = EscrowStatus::Refunded;
    rec.pack_into(&mut record_ai.try_borrow_mut_data()?)?;

    // Transfer the escrowed amount back to the depositor's captured destination.
    let transfer_ix = spl_token::instruction::transfer(
        &spl_token::id(),
        escrow_vault_ai.key,
        refund_dest_ai.key,
        escrow_authority_ai.key,
        &[],
        amount,
    )?;
    invoke_signed(
        &transfer_ix,
        &[
            escrow_vault_ai.clone(),
            refund_dest_ai.clone(),
            escrow_authority_ai.clone(),
            token_program.clone(),
        ],
        &[&[
            SEED_ESCROW_AUTHORITY,
            config_ai.key.as_ref(),
            &[escrow_auth_bump],
        ]],
    )?;

    msg!("dregg-lock: escrow refunded {} (deadline passed)", amount);
    Ok(())
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// Create a PDA-addressed account via a signed System `create_account` CPI:
/// fund it rent-exempt for `space` bytes and assign `owner`. `signer_seeds` are the
/// full seeds (including bump) of the account being created.
#[allow(clippy::too_many_arguments)]
fn create_pda_account<'a>(
    payer: &AccountInfo<'a>,
    new_account: &AccountInfo<'a>,
    system_program: &AccountInfo<'a>,
    owner: &Pubkey,
    space: usize,
    signer_seeds: &[&[u8]],
    rent: &Rent,
) -> ProgramResult {
    if system_program.key != &solana_program::system_program::id() {
        return Err(LockError::AccountMismatch.into());
    }
    let lamports = rent.minimum_balance(space);
    let ix = system_instruction::create_account(
        payer.key,
        new_account.key,
        lamports,
        space as u64,
        owner,
    );
    invoke_signed(
        &ix,
        &[payer.clone(), new_account.clone(), system_program.clone()],
        &[signer_seeds],
    )
    .map_err(ProgramError::from)
}

/// Count the number of DISTINCT configured oracle keys that ed25519-signed exactly
/// `message_hash`, by scanning the ed25519 native-program (precompile) instructions
/// in the current transaction via the instructions sysvar.
///
/// SECURITY: the runtime verifies every ed25519-program instruction BEFORE any
/// on-chain instruction executes, so every such instruction present is a genuine
/// (pubkey, message, signature). We resolve each (pubkey, message) exactly as the
/// precompile did — following the `*_instruction_index` reference (`u16::MAX` = the
/// ed25519 instruction's own data) — so the bytes we credit are the bytes that were
/// verified. We then keep only signatures whose message equals our reconstructed
/// `message_hash`, whose signer is an active configured oracle key, and dedupe by
/// signer. Anything else is silently not counted (fail-closed).
fn count_oracle_signers(
    instructions_ai: &AccountInfo,
    cfg: &VaultConfig,
    message_hash: &[u8; 32],
) -> Result<usize, LockError> {
    // The passed account MUST be the real instructions sysvar, or the scan is
    // meaningless — reject a spoofed account outright.
    if !instructions_sysvar::check_id(instructions_ai.key) {
        return Err(LockError::AccountMismatch);
    }

    // At most MAX_ORACLE_KEYS distinct signers can ever count; bound the buffer.
    let mut signers: Vec<[u8; 32]> = Vec::with_capacity(MAX_ORACLE_KEYS);

    for i in 0..MAX_TX_INSTRUCTIONS {
        let ix = match instructions_sysvar::load_instruction_at_checked(i, instructions_ai) {
            Ok(ix) => ix,
            Err(_) => break, // past the last instruction in the transaction
        };
        if ix.program_id != ed25519_program::id() {
            continue;
        }
        let refs = match parse_ed25519_refs(&ix.data) {
            Some(r) => r,
            None => continue, // malformed (can't happen post-precompile) — skip
        };
        for r in refs {
            let pk = match resolve_ref_bytes(
                &ix.data,
                instructions_ai,
                r.public_key_ix,
                r.public_key_off,
                PUBKEY_SERIALIZED_SIZE,
            ) {
                Some(b) => b,
                None => continue,
            };
            let msg = match resolve_ref_bytes(
                &ix.data,
                instructions_ai,
                r.message_ix,
                r.message_off,
                r.message_size as usize,
            ) {
                Some(b) => b,
                None => continue,
            };
            // Only a signature over EXACTLY our 32-byte hash authorizes this unlock.
            if msg.as_slice() != message_hash.as_slice() {
                continue;
            }
            let mut pubkey = [0u8; 32];
            pubkey.copy_from_slice(&pk);
            // Only ACTIVE configured oracle keys count (the zero-padded tail never
            // matches — `contains_oracle` scans only the first N).
            if !cfg.contains_oracle(&pubkey) {
                continue;
            }
            // DISTINCT signers only — a key that signs twice counts once.
            if signers.contains(&pubkey) {
                continue;
            }
            signers.push(pubkey);
        }
    }
    Ok(signers.len())
}

/// Resolve a `(instruction_index, offset, size)` reference from an ed25519 offsets
/// entry into the referenced bytes, mirroring the precompile's resolution:
/// `u16::MAX` reads the ed25519 instruction's own `current_data`; any other index
/// loads that transaction instruction via the sysvar. Returns `None` if the slice
/// is out of range.
fn resolve_ref_bytes(
    current_data: &[u8],
    instructions_ai: &AccountInfo,
    ins_index: u16,
    offset: u16,
    size: usize,
) -> Option<Vec<u8>> {
    let start = offset as usize;
    let end = start.checked_add(size)?;
    if ins_index == u16::MAX {
        current_data.get(start..end).map(|s| s.to_vec())
    } else {
        let ix =
            instructions_sysvar::load_instruction_at_checked(ins_index as usize, instructions_ai)
                .ok()?;
        ix.data.get(start..end).map(|s| s.to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The lock_id derivation is deterministic and unique-per-nonce: for a fixed
    /// program_id + config, distinct nonces yield distinct record PDAs (hence
    /// distinct lock_ids), and the same nonce reproduces the same PDA.
    #[test]
    fn lock_id_is_deterministic_and_unique_per_nonce() {
        let program_id = Pubkey::new_unique();
        let config = Pubkey::new_unique();
        let pda = |n: u64| {
            Pubkey::find_program_address(
                &[SEED_LOCK, config.as_ref(), &n.to_le_bytes()],
                &program_id,
            )
            .0
        };
        assert_eq!(pda(0), pda(0), "same nonce ⇒ same lock_id (deterministic)");
        assert_ne!(
            pda(0),
            pda(1),
            "distinct nonces ⇒ distinct lock_ids (unique)"
        );
        assert_ne!(pda(1), pda(2));
    }

    /// Distinct redeem_ids give distinct receipt PDAs (replay keyed per redeem_id).
    #[test]
    fn redeem_receipt_pda_is_per_redeem_id() {
        let program_id = Pubkey::new_unique();
        let config = Pubkey::new_unique();
        let pda = |id: [u8; 32]| {
            Pubkey::find_program_address(&[SEED_REDEEM, config.as_ref(), &id], &program_id).0
        };
        assert_ne!(pda([1u8; 32]), pda([2u8; 32]));
        assert_eq!(pda([7u8; 32]), pda([7u8; 32]));
    }
}
