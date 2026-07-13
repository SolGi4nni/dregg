//! End-to-end test of the TIMEOUT/REFUND ESCROW — the Solana twin of the EVM
//! `DreggVault` two-branch escrow, over `solana-program-test` (native BanksClient).
//!
//! It exercises the REAL exactly-once state machine, both polarities:
//!   * FILLED → RELEASE: an M-of-N ed25519 oracle attestation (the AssertProvenRoot
//!     analog) releases a locked escrow to the ring-matched recipient; the escrow is
//!     then terminal and a refund is refused.
//!   * UNFILLED → REFUND: after the per-escrow deadline the depositor reclaims the
//!     lock; the escrow is then terminal and a release is refused.
//!
//! The exactly-once teeth are all here: filled→release, unfilled→refund,
//! early-refund reverts, under-threshold ("proofless") release reverts, double
//! release / double refund revert, non-depositor refund reverts — and the
//! released-and-also-refunded (or refunded-and-also-released) state is unreachable.
//!
//! Deadlines are taken from wall clock: program-test's genesis `Clock.unix_timestamp`
//! is a real timestamp, so `now - 1h` is reliably PAST and `now + large` is reliably
//! FUTURE — no sysvar warping needed.

use std::time::{SystemTime, UNIX_EPOCH};

use dregg_solana_lock::attestation::unlock_message_hash;
use dregg_solana_lock::escrow::{EscrowRecord, EscrowStatus};
use dregg_solana_lock::instruction::LockInstruction;
use dregg_solana_lock::{
    process_instruction, SEED_CONFIG, SEED_ESCROW, SEED_ESCROW_AUTHORITY, SEED_ESCROW_VAULT,
    SEED_VAULT, SEED_VAULT_AUTHORITY,
};

use solana_program_test::{processor, BanksClient, ProgramTest};
use solana_sdk::{
    account::Account,
    instruction::{AccountMeta, Instruction, InstructionError},
    program_pack::Pack,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    system_instruction, system_program,
    transaction::{Transaction, TransactionError},
};

fn program_id() -> Pubkey {
    Pubkey::new_from_array([9u8; 32])
}

fn instructions_sysvar_id() -> Pubkey {
    solana_program::sysvar::instructions::id()
}

/// A wall-clock unix timestamp reliably in the PAST relative to the program clock.
fn past_deadline() -> i64 {
    (SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64)
        - 3600
}

/// A wall-clock unix timestamp reliably in the FUTURE relative to the program clock.
fn future_deadline() -> i64 {
    (SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64)
        + 10_000_000
}

fn ed25519_ix(kp: &Keypair, message: &[u8; 32]) -> Instruction {
    let sig = kp.sign_message(message);
    let sig_bytes: [u8; 64] = sig.as_ref().try_into().expect("64-byte signature");
    let pk: [u8; 32] = kp.pubkey().to_bytes();
    solana_ed25519_program::new_ed25519_instruction_with_signature(message, &sig_bytes, &pk)
}

// LockError discriminants (mirrors src/error.rs).
const ERR_THRESHOLD_NOT_MET: u32 = 11;
const ERR_ESCROW_NOT_LOCKED: u32 = 12;
const ERR_REFUND_BEFORE_DEADLINE: u32 = 13;
const ERR_ESCROW_FIELD_MISMATCH: u32 = 14;

fn custom_code(err: &solana_program_test::BanksClientError) -> Option<u32> {
    match err {
        solana_program_test::BanksClientError::TransactionError(
            TransactionError::InstructionError(_, InstructionError::Custom(c)),
        ) => Some(*c),
        _ => None,
    }
}

struct EscrowEnv {
    banks: BanksClient,
    payer: Keypair,
    program_id: Pubkey,
    config_pda: Pubkey,
    escrow_authority_pda: Pubkey,
    mint: Pubkey,
    user: Keypair,
    user_token: Pubkey,
    recipient_token: Pubkey,
    oracles: Vec<Keypair>,
    escrow_id: [u8; 32],
    locked: u64,
}

/// Init a 2-of-3 vault and `EscrowLock` `locked` under `escrow_id` with `deadline`.
async fn setup(locked: u64, escrow_id: [u8; 32], deadline: i64) -> EscrowEnv {
    let program_id = program_id();
    let mut pt = ProgramTest::new(
        "dregg_solana_lock",
        program_id,
        processor!(process_instruction),
    );

    let mint = Keypair::new();
    let mint_authority = Keypair::new();
    let user = Keypair::new();
    let user_token = Keypair::new();
    let recipient_owner = Keypair::new();
    let recipient_token = Keypair::new();

    let oracles: Vec<Keypair> = (0..3).map(|_| Keypair::new()).collect();
    let threshold: u8 = 2;
    let rent = solana_sdk::rent::Rent::default();

    // mint
    {
        let mut d = vec![0u8; spl_token::state::Mint::LEN];
        let s = spl_token::state::Mint {
            mint_authority: solana_program::program_option::COption::Some(mint_authority.pubkey()),
            supply: 1_000_000,
            decimals: 6,
            is_initialized: true,
            freeze_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Mint::pack(s, &mut d).unwrap();
        pt.add_account(
            mint.pubkey(),
            Account {
                lamports: rent.minimum_balance(d.len()),
                data: d,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );
    }
    // user token account (source + refund destination)
    {
        let mut d = vec![0u8; spl_token::state::Account::LEN];
        let s = spl_token::state::Account {
            mint: mint.pubkey(),
            owner: user.pubkey(),
            amount: 1_000_000,
            delegate: solana_program::program_option::COption::None,
            state: spl_token::state::AccountState::Initialized,
            is_native: solana_program::program_option::COption::None,
            delegated_amount: 0,
            close_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Account::pack(s, &mut d).unwrap();
        pt.add_account(
            user_token.pubkey(),
            Account {
                lamports: rent.minimum_balance(d.len()),
                data: d,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );
    }
    // recipient token account (release destination), empty
    {
        let mut d = vec![0u8; spl_token::state::Account::LEN];
        let s = spl_token::state::Account {
            mint: mint.pubkey(),
            owner: recipient_owner.pubkey(),
            amount: 0,
            delegate: solana_program::program_option::COption::None,
            state: spl_token::state::AccountState::Initialized,
            is_native: solana_program::program_option::COption::None,
            delegated_amount: 0,
            close_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Account::pack(s, &mut d).unwrap();
        pt.add_account(
            recipient_token.pubkey(),
            Account {
                lamports: rent.minimum_balance(d.len()),
                data: d,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );
    }

    let (mut banks, payer, blockhash) = pt.start().await;

    let (config_pda, _) = Pubkey::find_program_address(&[SEED_CONFIG], &program_id);
    let (vault_pda, _) =
        Pubkey::find_program_address(&[SEED_VAULT, config_pda.as_ref()], &program_id);
    let (vault_auth_pda, _) =
        Pubkey::find_program_address(&[SEED_VAULT_AUTHORITY, config_pda.as_ref()], &program_id);
    let (escrow_authority_pda, _) =
        Pubkey::find_program_address(&[SEED_ESCROW_AUTHORITY, config_pda.as_ref()], &program_id);

    // InitVault (2-of-3)
    let oracle_keys: Vec<[u8; 32]> = oracles.iter().map(|k| k.pubkey().to_bytes()).collect();
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
            oracle_threshold: threshold,
            oracle_keys,
        }
        .pack(),
    };
    let mut tx = Transaction::new_with_payer(&[init_ix], Some(&payer.pubkey()));
    tx.sign(&[&payer], blockhash);
    banks.process_transaction(tx).await.expect("InitVault");

    // EscrowLock
    let (escrow_vault, _) = Pubkey::find_program_address(
        &[SEED_ESCROW_VAULT, config_pda.as_ref(), &escrow_id],
        &program_id,
    );
    let (record_pda, _) =
        Pubkey::find_program_address(&[SEED_ESCROW, config_pda.as_ref(), &escrow_id], &program_id);
    let bh = banks.get_latest_blockhash().await.unwrap();
    let lock_ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new_readonly(config_pda, false),
            AccountMeta::new(user_token.pubkey(), false),
            AccountMeta::new(escrow_vault, false),
            AccountMeta::new_readonly(escrow_authority_pda, false),
            AccountMeta::new_readonly(user.pubkey(), true),
            AccountMeta::new(record_pda, false),
            AccountMeta::new_readonly(mint.pubkey(), false),
            AccountMeta::new_readonly(spl_token::id(), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: LockInstruction::EscrowLock {
            amount: locked,
            deadline,
            escrow_id,
        }
        .pack(),
    };
    let mut tx = Transaction::new_with_payer(&[lock_ix], Some(&payer.pubkey()));
    tx.sign(&[&payer, &user], bh);
    banks.process_transaction(tx).await.expect("EscrowLock");

    EscrowEnv {
        banks,
        payer,
        program_id,
        config_pda,
        escrow_authority_pda,
        mint: mint.pubkey(),
        user,
        user_token: user_token.pubkey(),
        recipient_token: recipient_token.pubkey(),
        oracles,
        escrow_id,
        locked,
    }
}

impl EscrowEnv {
    fn escrow_vault(&self) -> Pubkey {
        Pubkey::find_program_address(
            &[SEED_ESCROW_VAULT, self.config_pda.as_ref(), &self.escrow_id],
            &self.program_id,
        )
        .0
    }
    fn record_pda(&self) -> Pubkey {
        Pubkey::find_program_address(
            &[SEED_ESCROW, self.config_pda.as_ref(), &self.escrow_id],
            &self.program_id,
        )
        .0
    }
    fn release_hash(&self, amount: u64) -> [u8; 32] {
        unlock_message_hash(
            &self.mint.to_bytes(),
            amount,
            &self.recipient_token.to_bytes(),
            &self.escrow_id,
        )
    }
    fn release_ix(&self, amount: u64) -> Instruction {
        Instruction {
            program_id: self.program_id,
            accounts: vec![
                AccountMeta::new_readonly(self.config_pda, false),
                AccountMeta::new(self.record_pda(), false),
                AccountMeta::new(self.escrow_vault(), false),
                AccountMeta::new_readonly(self.escrow_authority_pda, false),
                AccountMeta::new(self.recipient_token, false),
                AccountMeta::new_readonly(spl_token::id(), false),
                AccountMeta::new_readonly(instructions_sysvar_id(), false),
            ],
            data: LockInstruction::EscrowRelease {
                amount,
                escrow_id: self.escrow_id,
            }
            .pack(),
        }
    }
    fn refund_ix(&self) -> Instruction {
        Instruction {
            program_id: self.program_id,
            accounts: vec![
                AccountMeta::new_readonly(self.config_pda, false),
                AccountMeta::new(self.record_pda(), false),
                AccountMeta::new(self.escrow_vault(), false),
                AccountMeta::new_readonly(self.escrow_authority_pda, false),
                AccountMeta::new(self.user_token, false),
                AccountMeta::new_readonly(self.user.pubkey(), true),
                AccountMeta::new_readonly(spl_token::id(), false),
            ],
            data: LockInstruction::EscrowRefund {
                escrow_id: self.escrow_id,
            }
            .pack(),
        }
    }

    /// Submit `ed_ixs` (oracle sigs) + release; payer signs.
    async fn try_release(
        &mut self,
        ed_ixs: Vec<Instruction>,
        amount: u64,
    ) -> Result<(), solana_program_test::BanksClientError> {
        let mut ixs = ed_ixs;
        ixs.push(self.release_ix(amount));
        let bh = self.banks.get_latest_blockhash().await.unwrap();
        let mut tx = Transaction::new_with_payer(&ixs, Some(&self.payer.pubkey()));
        tx.sign(&[&self.payer], bh);
        self.banks.process_transaction(tx).await
    }

    /// Submit a refund; payer + depositor(user) sign. `prefix` distinguishes an
    /// otherwise-identical retry so a second refund is a NEW transaction.
    async fn try_refund(
        &mut self,
        prefix: Vec<Instruction>,
    ) -> Result<(), solana_program_test::BanksClientError> {
        let mut ixs = prefix;
        ixs.push(self.refund_ix());
        let bh = self.banks.get_latest_blockhash().await.unwrap();
        let mut tx = Transaction::new_with_payer(&ixs, Some(&self.payer.pubkey()));
        tx.sign(&[&self.payer, &self.user], bh);
        self.banks.process_transaction(tx).await
    }

    async fn token_amount(&mut self, acct: Pubkey) -> u64 {
        let a = self.banks.get_account(acct).await.unwrap().unwrap();
        spl_token::state::Account::unpack(&a.data).unwrap().amount
    }
    async fn status(&mut self) -> EscrowStatus {
        let a = self
            .banks
            .get_account(self.record_pda())
            .await
            .unwrap()
            .unwrap();
        EscrowRecord::unpack(&a.data).unwrap().status
    }
    fn two_sigs(&self, a: usize, b: usize, amount: u64) -> Vec<Instruction> {
        let h = self.release_hash(amount);
        vec![
            ed25519_ix(&self.oracles[a], &h),
            ed25519_ix(&self.oracles[b], &h),
        ]
    }
}

// ─── POLARITY 1: FILLED → RELEASE ───────────────────────────────────────────────

#[tokio::test]
async fn filled_escrow_releases_to_recipient() {
    let mut env = setup(250_000, [0x01u8; 32], future_deadline()).await;
    let amount = 250_000u64;
    env.try_release(env.two_sigs(0, 1, amount), amount)
        .await
        .expect("release");

    assert_eq!(env.token_amount(env.recipient_token).await, 250_000);
    assert_eq!(env.token_amount(env.escrow_vault()).await, 0);
    assert_eq!(env.status().await, EscrowStatus::Released);
}

/// TOOTH: a Released escrow is terminal — a refund (past-deadline setup, so the
/// deadline guard is not what stops it) is refused. Released-and-also-refunded is
/// unreachable.
#[tokio::test]
async fn released_escrow_cannot_be_refunded() {
    let mut env = setup(250_000, [0x02u8; 32], past_deadline()).await;
    let amount = 250_000u64;
    env.try_release(env.two_sigs(0, 1, amount), amount)
        .await
        .expect("release");

    let err = env
        .try_refund(vec![])
        .await
        .expect_err("refund of released must fail");
    assert_eq!(custom_code(&err), Some(ERR_ESCROW_NOT_LOCKED));
    // Recipient keeps the funds; the escrow vault is empty.
    assert_eq!(env.token_amount(env.recipient_token).await, 250_000);
    assert_eq!(env.status().await, EscrowStatus::Released);
}

// ─── POLARITY 2: UNFILLED → REFUND ──────────────────────────────────────────────

#[tokio::test]
async fn unfilled_escrow_refunds_to_depositor_after_deadline() {
    let mut env = setup(250_000, [0x03u8; 32], past_deadline()).await;
    // user_token started at 1_000_000, minus 250_000 locked == 750_000.
    assert_eq!(env.token_amount(env.user_token).await, 750_000);

    env.try_refund(vec![]).await.expect("refund");
    assert_eq!(env.token_amount(env.user_token).await, 1_000_000); // full lock returned
    assert_eq!(env.token_amount(env.escrow_vault()).await, 0);
    assert_eq!(env.status().await, EscrowStatus::Refunded);
}

/// TOOTH: a Refunded escrow is terminal — a release with a fully valid attestation
/// is refused. Refunded-and-also-released is unreachable.
#[tokio::test]
async fn refunded_escrow_cannot_be_released() {
    let mut env = setup(250_000, [0x04u8; 32], past_deadline()).await;
    env.try_refund(vec![]).await.expect("refund");

    let amount = 250_000u64;
    let err = env
        .try_release(env.two_sigs(0, 1, amount), amount)
        .await
        .expect_err("release of refunded must fail");
    assert_eq!(custom_code(&err), Some(ERR_ESCROW_NOT_LOCKED));
    assert_eq!(env.token_amount(env.recipient_token).await, 0);
    assert_eq!(env.status().await, EscrowStatus::Refunded);
}

// ─── EXACTLY-ONCE TEETH ─────────────────────────────────────────────────────────

/// A refund BEFORE the deadline reverts (the timeout IS the condition).
#[tokio::test]
async fn refund_before_deadline_reverts() {
    let mut env = setup(250_000, [0x05u8; 32], future_deadline()).await;
    let err = env
        .try_refund(vec![])
        .await
        .expect_err("early refund must fail");
    assert_eq!(custom_code(&err), Some(ERR_REFUND_BEFORE_DEADLINE));
    assert_eq!(env.status().await, EscrowStatus::Locked);
}

/// A release WITHOUT a threshold of valid oracle signatures reverts (1 sig < M=2) —
/// the "proofless release" tooth.
#[tokio::test]
async fn release_with_insufficient_sigs_reverts() {
    let mut env = setup(250_000, [0x06u8; 32], future_deadline()).await;
    let amount = 250_000u64;
    let h = env.release_hash(amount);
    let one = vec![ed25519_ix(&env.oracles[0], &h)]; // only 1 of 2 required
    let err = env
        .try_release(one, amount)
        .await
        .expect_err("under-threshold release must fail");
    assert_eq!(custom_code(&err), Some(ERR_THRESHOLD_NOT_MET));
    assert_eq!(env.token_amount(env.recipient_token).await, 0);
    assert_eq!(env.status().await, EscrowStatus::Locked);
}

/// A double release reverts (the second sees a non-Locked status).
#[tokio::test]
async fn double_release_reverts() {
    let mut env = setup(250_000, [0x07u8; 32], future_deadline()).await;
    let amount = 250_000u64;
    env.try_release(env.two_sigs(0, 1, amount), amount)
        .await
        .expect("first release");
    // A distinct second tx (different oracle pair) still hits the terminal status.
    let err = env
        .try_release(env.two_sigs(0, 2, amount), amount)
        .await
        .expect_err("double release must fail");
    assert_eq!(custom_code(&err), Some(ERR_ESCROW_NOT_LOCKED));
    assert_eq!(env.token_amount(env.recipient_token).await, 250_000); // paid exactly once
}

/// A double refund reverts (the second sees a non-Locked status). The second tx is
/// made distinct by a 1-lamport self-transfer prefix so it is not a signature replay.
#[tokio::test]
async fn double_refund_reverts() {
    let mut env = setup(250_000, [0x08u8; 32], past_deadline()).await;
    env.try_refund(vec![]).await.expect("first refund");
    let bump = system_instruction::transfer(&env.payer.pubkey(), &env.payer.pubkey(), 1);
    let err = env
        .try_refund(vec![bump])
        .await
        .expect_err("double refund must fail");
    assert_eq!(custom_code(&err), Some(ERR_ESCROW_NOT_LOCKED));
    assert_eq!(env.token_amount(env.user_token).await, 1_000_000); // refunded exactly once
}

/// A refund by a non-depositor reverts. Here the refund destination account is not
/// the recorded one (a stranger's account), so the field check fails closed.
#[tokio::test]
async fn refund_to_wrong_destination_reverts() {
    let mut env = setup(250_000, [0x09u8; 32], past_deadline()).await;
    // Build a refund whose destination is the RECIPIENT token account (not the
    // captured user_token) — the record's refund_destination binding rejects it.
    let bad = Instruction {
        program_id: env.program_id,
        accounts: vec![
            AccountMeta::new_readonly(env.config_pda, false),
            AccountMeta::new(env.record_pda(), false),
            AccountMeta::new(env.escrow_vault(), false),
            AccountMeta::new_readonly(env.escrow_authority_pda, false),
            AccountMeta::new(env.recipient_token, false), // wrong destination
            AccountMeta::new_readonly(env.user.pubkey(), true),
            AccountMeta::new_readonly(spl_token::id(), false),
        ],
        data: LockInstruction::EscrowRefund {
            escrow_id: env.escrow_id,
        }
        .pack(),
    };
    let bh = env.banks.get_latest_blockhash().await.unwrap();
    let mut tx = Transaction::new_with_payer(&[bad], Some(&env.payer.pubkey()));
    tx.sign(&[&env.payer, &env.user], bh);
    let err = env
        .banks
        .process_transaction(tx)
        .await
        .expect_err("wrong destination must fail");
    assert_eq!(custom_code(&err), Some(ERR_ESCROW_FIELD_MISMATCH));
    assert_eq!(env.status().await, EscrowStatus::Locked);
}
