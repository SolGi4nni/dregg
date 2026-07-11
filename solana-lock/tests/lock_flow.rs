//! Integration test of the Lock path over `solana-program-test` (native BanksClient,
//! no SBF): InitVault → mint $DREGG to a user → Lock → assert the on-chain
//! lock-record account is exactly the 72-byte layout the dregg relayer decodes.
//!
//! This exercises the real CPI path (System create_account + SPL token transfer +
//! SPL initialize_account3) against the SPL Token program loaded into the test bank.

use dregg_solana_lock::instruction::LockInstruction;
use dregg_solana_lock::record::{decode_lock_record, LOCK_RECORD_LEN};
use dregg_solana_lock::state::VaultConfig;
use dregg_solana_lock::{
    process_instruction, SEED_CONFIG, SEED_LOCK, SEED_VAULT, SEED_VAULT_AUTHORITY,
};

use solana_program_test::{processor, ProgramTest};
use solana_sdk::{
    account::Account,
    instruction::{AccountMeta, Instruction},
    program_pack::Pack,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    system_program,
    transaction::Transaction,
};

fn program_id() -> Pubkey {
    // fixed id so PDAs are stable across the test
    Pubkey::new_from_array([9u8; 32])
}

#[tokio::test]
async fn lock_writes_decodable_72_byte_record() {
    let program_id = program_id();
    let mut pt = ProgramTest::new(
        "dregg_solana_lock",
        program_id,
        processor!(process_instruction),
    );

    // The $DREGG mint, pre-created in the bank (initialized, authority = mint_auth).
    let mint = Keypair::new();
    let mint_authority = Keypair::new();
    let user = Keypair::new();
    let user_token = Keypair::new();
    let unlock_authority = Pubkey::new_from_array([0x55u8; 32]);

    // Pre-seed the mint account and the user's token account with balance, so the
    // test focuses on InitVault + Lock (mint setup is not the code under test).
    let rent = solana_sdk::rent::Rent::default();
    {
        // mint account
        let mut mint_data = vec![0u8; spl_token::state::Mint::LEN];
        let mint_state = spl_token::state::Mint {
            mint_authority: solana_program::program_option::COption::Some(mint_authority.pubkey()),
            supply: 1_000_000,
            decimals: 6,
            is_initialized: true,
            freeze_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Mint::pack(mint_state, &mut mint_data).unwrap();
        pt.add_account(
            mint.pubkey(),
            Account {
                lamports: rent.minimum_balance(mint_data.len()),
                data: mint_data,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );

        // user token account holding 500_000 $DREGG
        let mut acct_data = vec![0u8; spl_token::state::Account::LEN];
        let acct_state = spl_token::state::Account {
            mint: mint.pubkey(),
            owner: user.pubkey(),
            amount: 500_000,
            delegate: solana_program::program_option::COption::None,
            state: spl_token::state::AccountState::Initialized,
            is_native: solana_program::program_option::COption::None,
            delegated_amount: 0,
            close_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Account::pack(acct_state, &mut acct_data).unwrap();
        pt.add_account(
            user_token.pubkey(),
            Account {
                lamports: rent.minimum_balance(acct_data.len()),
                data: acct_data,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );
    }

    let (mut banks, payer, recent_blockhash) = pt.start().await;

    // PDAs
    let (config_pda, _) = Pubkey::find_program_address(&[SEED_CONFIG], &program_id);
    let (vault_pda, _) =
        Pubkey::find_program_address(&[SEED_VAULT, config_pda.as_ref()], &program_id);
    let (vault_auth_pda, _) =
        Pubkey::find_program_address(&[SEED_VAULT_AUTHORITY, config_pda.as_ref()], &program_id);

    // --- InitVault ---
    let init_ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new(config_pda, false),
            AccountMeta::new_readonly(mint.pubkey(), false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(vault_auth_pda, false),
            AccountMeta::new_readonly(spl_token::id(), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: LockInstruction::InitVault {
            unlock_authority: unlock_authority.to_bytes(),
        }
        .pack(),
    };
    let mut tx = Transaction::new_with_payer(&[init_ix], Some(&payer.pubkey()));
    tx.sign(&[&payer], recent_blockhash);
    banks.process_transaction(tx).await.expect("InitVault");

    // config was written correctly
    let cfg_acct = banks.get_account(config_pda).await.unwrap().unwrap();
    assert_eq!(cfg_acct.owner, program_id);
    let cfg = VaultConfig::unpack(&cfg_acct.data).unwrap();
    assert_eq!(cfg.mint, mint.pubkey().to_bytes());
    assert_eq!(cfg.vault_token_account, vault_pda.to_bytes());
    assert_eq!(cfg.nonce, 0);

    // --- Lock 250_000 for a dregg recipient ---
    let dregg_recipient = [0xEEu8; 32];
    let amount: u64 = 250_000;
    let nonce = cfg.nonce;
    let (record_pda, _) = Pubkey::find_program_address(
        &[SEED_LOCK, config_pda.as_ref(), &nonce.to_le_bytes()],
        &program_id,
    );

    let recent_blockhash = banks.get_latest_blockhash().await.unwrap();
    let lock_ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new(config_pda, false),
            AccountMeta::new(user_token.pubkey(), false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(user.pubkey(), true),
            AccountMeta::new(record_pda, false),
            AccountMeta::new_readonly(spl_token::id(), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: LockInstruction::Lock {
            amount,
            dregg_recipient,
        }
        .pack(),
    };
    let mut tx = Transaction::new_with_payer(&[lock_ix], Some(&payer.pubkey()));
    tx.sign(&[&payer, &user], recent_blockhash);
    banks.process_transaction(tx).await.expect("Lock");

    // (a) the record account is program-owned and exactly 72 bytes.
    let rec = banks.get_account(record_pda).await.unwrap().unwrap();
    assert_eq!(
        rec.owner, program_id,
        "relayer requires owner == lock_program"
    );
    assert_eq!(rec.data.len(), LOCK_RECORD_LEN, "must be exactly 72 bytes");

    // (b) it decodes via the relayer's contract to the right (lock_id, recipient, amount).
    let (lock_id, recipient, amt) =
        decode_lock_record(&rec.data).expect("relayer decode_lock_record succeeds");
    assert_eq!(
        lock_id,
        record_pda.to_bytes(),
        "lock_id == record PDA pubkey"
    );
    assert_eq!(recipient, dregg_recipient);
    assert_eq!(amt, amount);

    // (c) the tokens actually moved into the vault.
    let vault_acct = banks.get_account(vault_pda).await.unwrap().unwrap();
    let vault_state = spl_token::state::Account::unpack(&vault_acct.data).unwrap();
    assert_eq!(vault_state.amount, amount);
    assert_eq!(vault_state.mint, mint.pubkey());

    // (d) the nonce advanced, so the next lock gets a fresh lock_id.
    let cfg2 =
        VaultConfig::unpack(&banks.get_account(config_pda).await.unwrap().unwrap().data).unwrap();
    assert_eq!(cfg2.nonce, 1);
}
