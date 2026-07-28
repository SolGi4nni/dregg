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
    process_instruction, settlement_vk_digest, SEED_PROVEN_ROOT, SEED_SETTLEMENT,
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
    /// The 25-lane statement as canonical BabyBear u32s -- the wire shape since
    /// 2026-07-28 (see `instruction.rs`'s flag-day note).
    lanes: [u32; 25],
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

/// A fixture public input is a decimal canonical BabyBear residue. Parsing it as a
/// u32 is total on the real fixture and asserts the property the wire now relies on.
fn dec_lane(s: &str) -> u32 {
    let v: u64 = s.parse().unwrap();
    assert!(
        v < 2013265921,
        "fixture lane {v} is not a canonical BabyBear residue"
    );
    v as u32
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
    let lanes_vec: Vec<u32> = j["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| dec_lane(x.as_str().unwrap()))
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
    let mut lanes = [0u32; 25];
    lanes.copy_from_slice(&lanes_vec);

    Fixture {
        a,
        b,
        c,
        commitment,
        commitment_pok,
        lanes,
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
    init_ix_with_vk_hash(payer, genesis_root, settlement_vk_digest())
}

fn init_ix_with_vk_hash(payer: &Pubkey, genesis_root: [u32; 8], vk_hash: [u8; 32]) -> Instruction {
    let data = SettlementInstruction::InitSettlement {
        genesis_root,
        vk_hash,
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

fn settle_ix(fx: &Fixture, lanes: [u32; 25], a: [u8; 64], payer: &Pubkey) -> Instruction {
    // The final-root marker is derived from the STATEMENT's final lanes (8..16),
    // so a forged statement points at a different (never-created) marker.
    let final_lanes: [u32; 8] = lanes[8..16].try_into().unwrap();
    let data = SettlementInstruction::Settle {
        a,
        b: fx.b,
        c: fx.c,
        commitment: fx.commitment,
        commitment_pok: fx.commitment_pok,
        lanes,
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

/// ⚑ **THE SETTLE TRANSACTION MUST FIT IN A SOLANA PACKET, AND NOTHING ELSE HERE CAN TELL US.**
///
/// This gate exists because the two tests below are green and *structurally cannot* go red on it:
/// `ProgramTest::new(..., processor!(...))` runs the processor natively (so the `solana_bn254`
/// syscall CU meter is never charged) and hands a `Transaction` OBJECT to `BanksClient`, which never
/// wire-serializes it. `PACKET_DATA_SIZE` appeared nowhere in this repository before this test.
///
/// A validator drops any transaction whose serialized form exceeds `PACKET_DATA_SIZE` (1232 =
/// 1280 MTU − 40 IPv6 − 8 UDP, `solana-packet-2.2.1/src/lib.rs:32`).
///
/// ## The measurement, and what closed it
///
/// This test was RED at HEAD from the day it was written until 2026-07-28, at **1495 serialized
/// bytes, over by 263** — the Solana settle had never been broadcast because it *could not* be.
/// The cause was the wire encoding of the 25 statement lanes as full 32-byte big-endian Groth16
/// scalars: 800 bytes, of which the processor REQUIRED 700 to be zero (`input_to_lane` rejected
/// any input with a non-zero high 28 bytes, since a settlement lane is a canonical BabyBear
/// residue `< 2^31`). The lanes now go on the wire as the `u32`s they provably are — 25 × 4 = 100 B
/// — putting the transaction at **795 bytes with 437 to spare**, ComputeBudget instruction and all.
///
/// That was recorded as "a WIRE-FORMAT decision and therefore ember's call". Per CLAUDE.md the
/// constituency was invented: nothing held the old format, and deleting 700 bytes the program had
/// already proved were zero is not a trade — it also NARROWS the wire (a non-canonical scalar is
/// now unrepresentable rather than merely rejected). See `instruction.rs` for the flag day.
///
/// The bound is asserted from both sides: over `PACKET_DATA_SIZE` fails, and so does a transaction
/// so small it suggests the payload silently stopped carrying the statement.
#[tokio::test]
async fn settle_transaction_fits_in_a_solana_packet() {
    let fx = load_fixture();
    let payer = Keypair::new();

    // The runbook's real settle tx: a ComputeBudget limit (the settle exceeds the
    // 200,000-CU default, `docs/ops/DEPLOY-SOLANA-COSMOS-TESTNET.md` §1.7) + the settle.
    let cu_ix = ComputeBudgetInstruction::set_compute_unit_limit(600_000);
    let settle = settle_ix(&fx, fx.lanes, fx.a, &payer.pubkey());
    let mut tx = Transaction::new_with_payer(&[cu_ix, settle.clone()], Some(&payer.pubkey()));
    tx.sign(&[&payer], Hash::default());

    let wire = bincode::serialize(&tx).expect("a Transaction serializes with bincode");
    let len = wire.len();

    assert!(
        len <= PACKET_DATA_SIZE,
        "settle transaction is {len} serialized bytes against PACKET_DATA_SIZE = {PACKET_DATA_SIZE} \
         (over by {}). A validator will DROP it; the settle cannot be broadcast at all.",
        len.saturating_sub(PACKET_DATA_SIZE)
    );

    // Anti-vacuity: the gate must not pass because the payload stopped carrying the
    // statement. The settle instruction data is tag + 384 B proof + 25 * 4 B lanes.
    assert_eq!(
        settle.data.len(),
        1 + 384 + 25 * 4,
        "the settle payload must still carry the whole proof and all 25 lanes"
    );
    assert_eq!(settle.data.len(), 485);

    // The transaction size is deterministic (fixed-size signature, pubkeys and
    // payload), so pin it exactly rather than only bounding it: an exact figure
    // catches silent payload growth long before it reaches the 1232-byte cliff.
    assert_eq!(
        len, 795,
        "settle transaction size changed; it was 1495 B (over by 263) before the u32 \
         lane encoding and 795 B (437 to spare) after"
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

    // settle with the REAL proof + REAL 25 lanes.
    let mut tx = Transaction::new_with_payer(
        &[settle_ix(&fx, fx.lanes, fx.a, &payer.pubkey())],
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
    let mut forged_lanes = fx.lanes;
    // bump final_root[0] (lane 8) by one -- still canonical, wrong statement.
    forged_lanes[8] += 1;
    assert!(
        forged_lanes[8] < 2013265921,
        "the forgery must stay canonical"
    );
    let mut tx = Transaction::new_with_payer(
        &[settle_ix(&fx, forged_lanes, fx.a, &payer.pubkey())],
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
        &[settle_ix(&fx, fx.lanes, forged_a, &payer.pubkey())],
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
