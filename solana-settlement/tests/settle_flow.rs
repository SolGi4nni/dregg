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
use dregg_solana_settlement::state::{packed_root, ProvenRootMarker, SettlementState};
use dregg_solana_settlement::{
    dev_ceremony_vk_hash, process_instruction, SEED_PROVEN_ROOT, SEED_SETTLEMENT,
};

use solana_program_test::{processor, ProgramTest};
use solana_sdk::{
    compute_budget::ComputeBudgetInstruction,
    hash::Hash,
    instruction::{AccountMeta, Instruction},
    packet::PACKET_DATA_SIZE,
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

fn marker_pda(lanes: &[u32; 8]) -> Pubkey {
    Pubkey::find_program_address(&[SEED_PROVEN_ROOT, &packed_root(lanes)], &program_id()).0
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
            AccountMeta::new(marker_pda(&genesis_root), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data,
    }
}

fn settle_ix(fx: &Fixture, inputs: [[u8; 32]; 25], a: [u8; 64], payer: &Pubkey) -> Instruction {
    // The final-root marker is derived from the STATEMENT's final lanes (inputs
    // 8..16), so a forged statement points at a different (never-created) marker.
    let mut final_lanes = [0u32; 8];
    for i in 0..8 {
        let b = inputs[8 + i];
        final_lanes[i] = u32::from_be_bytes([b[28], b[29], b[30], b[31]]);
    }
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
        accounts: vec![
            AccountMeta::new(state_pda(), false),
            AccountMeta::new(*payer, true),
            AccountMeta::new(marker_pda(&final_lanes), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data,
    }
}

fn assert_proven_ix(lanes: &[u32; 8]) -> Instruction {
    Instruction {
        program_id: program_id(),
        accounts: vec![AccountMeta::new_readonly(marker_pda(lanes), false)],
        data: SettlementInstruction::AssertProvenRoot {
            root: packed_root(lanes),
        }
        .pack(),
    }
}

/// ⚑ **THE SETTLE TRANSACTION DOES NOT FIT IN A SOLANA PACKET, AND NOTHING HERE COULD TELL US.**
///
/// This gate exists because the two tests below are green and *structurally cannot* go red on it:
/// `ProgramTest::new(..., processor!(...))` runs the processor natively (so the `solana_bn254`
/// syscall CU meter is never charged) and hands a `Transaction` OBJECT to `BanksClient`, which never
/// wire-serializes it. `PACKET_DATA_SIZE` appeared nowhere in this repository before this test.
///
/// A validator drops any transaction whose serialized form exceeds `PACKET_DATA_SIZE` (1232 =
/// 1280 MTU − 40 IPv6 − 8 UDP, `solana-packet-2.2.1/src/lib.rs:32`). The settle payload carries the
/// 25 statement lanes as full 32-byte big-endian scalars (`SETTLE_LEN`, `instruction.rs:24`), which
/// is 800 bytes of the ~1184-byte payload — and the runbook additionally requires a prepended
/// `ComputeBudget` instruction, because the settle exceeds the 200,000-CU default
/// (`docs/ops/DEPLOY-SOLANA-COSMOS-TESTNET.md` §1.7).
///
/// ⚠ **THIS TEST IS EXPECTED RED AT HEAD.** That is the finding, not a flaw in the test: the Solana
/// settle has never been broadcast because it *cannot* be. It is deliberately NOT `#[ignore]`d —
/// an ignored gate is one nobody reads. It goes green when the wire encoding carries the lanes as
/// canonical `u32` (25 × 4 = 100 B instead of 800 B), which is a WIRE-FORMAT decision and therefore
/// ember's call, not a change this test makes on its own.
#[tokio::test]
async fn settle_transaction_fits_in_a_solana_packet() {
    let fx = load_fixture();
    let payer = Keypair::new();

    // The runbook's real settle tx: ComputeBudget limit + the settle instruction.
    let cu_ix = ComputeBudgetInstruction::set_compute_unit_limit(600_000);
    let mut tx = Transaction::new_with_payer(
        &[cu_ix, settle_ix(&fx, fx.inputs, fx.a, &payer.pubkey())],
        Some(&payer.pubkey()),
    );
    tx.sign(&[&payer], Hash::default());

    let wire = bincode::serialize(&tx).expect("a Transaction serializes with bincode");
    let len = wire.len();

    assert!(
        len <= PACKET_DATA_SIZE,
        "settle transaction is {len} serialized bytes against PACKET_DATA_SIZE = {PACKET_DATA_SIZE} \
         (over by {}). A validator will DROP it; the settle cannot be broadcast at all. The 25 \
         statement lanes occupy 800 B of the payload as 32-byte scalars and are canonical u32 \
         values (100 B) on the wire.",
        len.saturating_sub(PACKET_DATA_SIZE)
    );
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
    let mut tx = Transaction::new_with_payer(
        &[settle_ix(&fx, fx.inputs, fx.a, &payer.pubkey())],
        Some(&payer.pubkey()),
    );
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

    // REGISTRY: the final root is now recorded (`isProvenRoot`) -- a marker PDA
    // exists, program-owned, carrying the height. The genesis anchor too.
    let final_marker = banks
        .get_account(marker_pda(&fx.final_root))
        .await
        .unwrap()
        .expect("final root recorded in registry");
    assert_eq!(final_marker.owner, program_id());
    assert_eq!(
        ProvenRootMarker::unpack(&final_marker.data).unwrap().height,
        2
    );
    assert!(
        banks
            .get_account(marker_pda(&fx.genesis_root))
            .await
            .unwrap()
            .is_some(),
        "genesis anchor recorded at init"
    );

    // GATE: AssertProvenRoot succeeds for the proven final root (the CPI-able
    // `isProvenRoot` a consumer program gates on)...
    let mut tx =
        Transaction::new_with_payer(&[assert_proven_ix(&fx.final_root)], Some(&payer.pubkey()));
    tx.sign(&[&payer], blockhash);
    banks
        .process_transaction(tx)
        .await
        .expect("AssertProvenRoot must accept a proven root");

    // ...and REJECTS an unproven root (THE NOMAD LAW): no marker PDA exists.
    let unproven = [999u32, 0, 0, 0, 0, 0, 0, 0];
    let mut tx = Transaction::new_with_payer(&[assert_proven_ix(&unproven)], Some(&payer.pubkey()));
    tx.sign(&[&payer], blockhash);
    assert!(
        banks.process_transaction(tx).await.is_err(),
        "AssertProvenRoot must reject an unproven root"
    );
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
        &[settle_ix(&fx, forged_inputs, fx.a, &payer.pubkey())],
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
        &[settle_ix(&fx, fx.inputs, forged_a, &payer.pubkey())],
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
