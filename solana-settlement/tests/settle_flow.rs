//! Both-polarity integration test over `solana-program-test` (native BanksClient):
//! the settlement program VERIFIES the REAL dregg fixture proof on-chain and
//! advances the root, and REJECTS a forged proof (no root advance).
//!
//! The fixture (`chain/test/fixtures/settlement_groth16.json`) is the SAME real
//! 2-turn dregg apex proof that settled on Base-Sepolia
//! (tx 0xbd2cac6a...e963b, `chain/DEPLOYMENTS.md`). The `alt_bn128` verification
//! runs here on the identical ark-bn254 arithmetic the on-chain
//! `sol_alt_bn128_*` syscalls use -- so a pass here is the real Groth16 verify
//! path exercised end-to-end (the host-side verify-path check), and the SAME code
//! compiles to SBF via `cargo build-sbf` for on-chain execution.

use dregg_solana_settlement::instruction::SettlementInstruction;
use dregg_solana_settlement::state::SettlementState;
use dregg_solana_settlement::{dev_ceremony_vk_hash, process_instruction, SEED_SETTLEMENT};

use solana_program_test::{processor, ProgramTest};
use solana_sdk::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    system_program,
    transaction::Transaction,
};

fn program_id() -> Pubkey {
    Pubkey::new_from_array([7u8; 32])
}

// --- fixture parsing ---------------------------------------------------------

struct Fixture {
    a: [u8; 64],
    b: [u8; 128],
    c: [u8; 64],
    commitment: [u8; 64],
    commitment_pok: [u8; 64],
    inputs: [[u8; 32]; 25],
    genesis_root: [u32; 8],
    final_root: [u32; 8],
}

fn hex_be32(s: &str) -> [u8; 32] {
    let s = s.trim_start_matches("0x");
    let s = format!("{:0>64}", s);
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap();
    }
    out
}

fn dec_be32(s: &str) -> [u8; 32] {
    let v: u128 = s.parse().unwrap();
    let mut out = [0u8; 32];
    out[16..32].copy_from_slice(&v.to_be_bytes());
    out
}

fn lanes8(v: &serde_json::Value) -> [u32; 8] {
    let arr = v.as_array().unwrap();
    let mut out = [0u32; 8];
    for (i, x) in arr.iter().enumerate() {
        out[i] = x.as_u64().unwrap() as u32;
    }
    out
}

fn load_fixture() -> Fixture {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../chain/test/fixtures/settlement_groth16.json"
    );
    let text = std::fs::read_to_string(path).expect("read fixture");
    let j: serde_json::Value = serde_json::from_str(&text).unwrap();

    let proof: Vec<[u8; 32]> = j["proof"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| hex_be32(x.as_str().unwrap()))
        .collect();
    let comm: Vec<[u8; 32]> = j["commitments"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| hex_be32(x.as_str().unwrap()))
        .collect();
    let pok: Vec<[u8; 32]> = j["commitment_pok"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| hex_be32(x.as_str().unwrap()))
        .collect();
    let inputs_vec: Vec<[u8; 32]> = j["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| dec_be32(x.as_str().unwrap()))
        .collect();

    let mut a = [0u8; 64];
    a[..32].copy_from_slice(&proof[0]);
    a[32..].copy_from_slice(&proof[1]);
    let mut b = [0u8; 128];
    b[..32].copy_from_slice(&proof[2]);
    b[32..64].copy_from_slice(&proof[3]);
    b[64..96].copy_from_slice(&proof[4]);
    b[96..].copy_from_slice(&proof[5]);
    let mut c = [0u8; 64];
    c[..32].copy_from_slice(&proof[6]);
    c[32..].copy_from_slice(&proof[7]);
    let mut commitment = [0u8; 64];
    commitment[..32].copy_from_slice(&comm[0]);
    commitment[32..].copy_from_slice(&comm[1]);
    let mut commitment_pok = [0u8; 64];
    commitment_pok[..32].copy_from_slice(&pok[0]);
    commitment_pok[32..].copy_from_slice(&pok[1]);
    let mut inputs = [[0u8; 32]; 25];
    for (i, s) in inputs_vec.iter().enumerate() {
        inputs[i] = *s;
    }

    Fixture {
        a,
        b,
        c,
        commitment,
        commitment_pok,
        inputs,
        genesis_root: lanes8(&j["genesis_root"]),
        final_root: lanes8(&j["final_root"]),
    }
}

// --- harness -----------------------------------------------------------------

fn state_pda() -> Pubkey {
    Pubkey::find_program_address(&[SEED_SETTLEMENT], &program_id()).0
}

fn init_ix(payer: &Pubkey, genesis_root: [u32; 8]) -> Instruction {
    let data = SettlementInstruction::InitSettlement {
        genesis_root,
        vk_hash: dev_ceremony_vk_hash(),
    }
    .pack();
    Instruction {
        program_id: program_id(),
        accounts: vec![
            AccountMeta::new(*payer, true),
            AccountMeta::new(state_pda(), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data,
    }
}

fn settle_ix(fx: &Fixture, inputs: [[u8; 32]; 25], a: [u8; 64]) -> Instruction {
    let data = SettlementInstruction::Settle {
        a,
        b: fx.b,
        c: fx.c,
        commitment: fx.commitment,
        commitment_pok: fx.commitment_pok,
        inputs,
    }
    .pack();
    Instruction {
        program_id: program_id(),
        accounts: vec![AccountMeta::new(state_pda(), false)],
        data,
    }
}

#[tokio::test]
async fn real_proof_settles_and_advances_root() {
    let fx = load_fixture();
    let pt = ProgramTest::new(
        "dregg_solana_settlement",
        program_id(),
        processor!(process_instruction),
    );
    let (banks, payer, blockhash) = pt.start().await;

    // init: pin genesis = fixture genesis_root, vk_hash = the EVM dev pin.
    let mut tx = Transaction::new_with_payer(
        &[init_ix(&payer.pubkey(), fx.genesis_root)],
        Some(&payer.pubkey()),
    );
    tx.sign(&[&payer], blockhash);
    banks.process_transaction(tx).await.expect("init");

    // settle with the REAL proof + REAL 25 inputs.
    let mut tx =
        Transaction::new_with_payer(&[settle_ix(&fx, fx.inputs, fx.a)], Some(&payer.pubkey()));
    tx.sign(&[&payer], blockhash);
    banks
        .process_transaction(tx)
        .await
        .expect("real proof must verify on-chain");

    // The root advanced to final_root, height accumulated num_turns (= 2).
    let acct = banks.get_account(state_pda()).await.unwrap().unwrap();
    let state = SettlementState::unpack(&acct.data).unwrap();
    assert_eq!(
        state.proven_root, fx.final_root,
        "proven_root -> final_root"
    );
    assert_eq!(state.proven_height, 2, "height accumulated num_turns");
    assert_eq!(state.genesis_root, fx.genesis_root);
}

#[tokio::test]
async fn forged_proof_rejected_root_unchanged() {
    let fx = load_fixture();
    let pt = ProgramTest::new(
        "dregg_solana_settlement",
        program_id(),
        processor!(process_instruction),
    );
    let (banks, payer, blockhash) = pt.start().await;

    let mut tx = Transaction::new_with_payer(
        &[init_ix(&payer.pubkey(), fx.genesis_root)],
        Some(&payer.pubkey()),
    );
    tx.sign(&[&payer], blockhash);
    banks.process_transaction(tx).await.expect("init");

    // FORGERY 1 (altered statement): claim a DIFFERENT final root than the proof
    // attests. Continuity still holds (genesis unchanged), so this isolates the
    // crypto check -- the MSM differs, the pairing fails, the proof is rejected.
    let mut forged_inputs = fx.inputs;
    // bump final_root[0] (input lane 8) by one -- still canonical, wrong statement.
    forged_inputs[8] = {
        let mut b = fx.inputs[8];
        b[31] = b[31].wrapping_add(1);
        b
    };
    let mut tx = Transaction::new_with_payer(
        &[settle_ix(&fx, forged_inputs, fx.a)],
        Some(&payer.pubkey()),
    );
    tx.sign(&[&payer], blockhash);
    assert!(
        banks.process_transaction(tx).await.is_err(),
        "a proof for a DIFFERENT final root must be rejected"
    );

    // FORGERY 2 (tampered proof point): flip a byte of A. Off the pairing, reject.
    let mut forged_a = fx.a;
    forged_a[0] ^= 0x01;
    let mut tx = Transaction::new_with_payer(
        &[settle_ix(&fx, fx.inputs, forged_a)],
        Some(&payer.pubkey()),
    );
    tx.sign(&[&payer], blockhash);
    assert!(
        banks.process_transaction(tx).await.is_err(),
        "a tampered proof point must be rejected"
    );

    // The root did NOT advance: still the genesis anchor, height 0 (fail-closed).
    let acct = banks.get_account(state_pda()).await.unwrap().unwrap();
    let state = SettlementState::unpack(&acct.data).unwrap();
    assert_eq!(
        state.proven_root, fx.genesis_root,
        "forged proof advanced nothing"
    );
    assert_eq!(state.proven_height, 0);
}
