//! THE DEMONSTRATION: a real dregg Groth16 proof verifies inside a Cosmos runtime.
//!
//! This routes instantiate/execute/query through a full `cw-multi-test` App — the
//! CosmWasm contract executes exactly as it would on a Cosmos SDK `x/wasm` chain
//! (blocks, addressing, gas-metered storage) — and settles the SAME real fixture
//! the EVM Foundry test settles: `cosmos-settlement/tests/fixtures/
//! settlement_groth16.json` (copied byte-for-byte from `chain/test/fixtures/`).
//!
//! Both polarities are asserted:
//!   * the REAL proof over the pinned 25-lane statement is ACCEPTED and advances
//!     the proven root/height;
//!   * forged variants (wrong final root, tampered proof point, tampered
//!     commitment) are REJECTED by the real pairing check, and nothing settles.

use cosmwasm_std::Addr;
use cw_multi_test::{App, ContractWrapper, Executor};
use serde_json::Value;

use cosmos_settlement::msg::{
    BoolResponse, ExecuteMsg, HeightResponse, InstantiateMsg, LanesResponse, RootResponse,
};
use cosmos_settlement::{execute, instantiate, query};

const FIXTURE: &str = include_str!("fixtures/settlement_groth16.json");

struct Fixture {
    proof: [String; 8],
    commitments: [String; 2],
    commitment_pok: [String; 2],
    genesis_root: [u32; 8],
    final_root: [u32; 8],
    num_turns: u32,
    chain_digest: [u32; 8],
}

fn str_arr<const N: usize>(v: &Value, key: &str) -> [String; N] {
    let arr = v[key].as_array().expect("array field");
    assert_eq!(arr.len(), N, "field {key} wrong length");
    core::array::from_fn(|i| arr[i].as_str().expect("string element").to_string())
}

fn u32_arr(v: &Value, key: &str) -> [u32; 8] {
    let arr = v[key].as_array().expect("array field");
    assert_eq!(arr.len(), 8, "field {key} wrong length");
    core::array::from_fn(|i| arr[i].as_u64().expect("number element") as u32)
}

fn load_fixture() -> Fixture {
    let v: Value = serde_json::from_str(FIXTURE).expect("valid fixture json");
    Fixture {
        proof: str_arr::<8>(&v, "proof"),
        commitments: str_arr::<2>(&v, "commitments"),
        commitment_pok: str_arr::<2>(&v, "commitment_pok"),
        genesis_root: u32_arr(&v, "genesis_root"),
        final_root: u32_arr(&v, "final_root"),
        num_turns: v["num_turns"].as_u64().expect("num_turns") as u32,
        chain_digest: u32_arr(&v, "chain_digest"),
    }
}

fn settle_msg(f: &Fixture) -> ExecuteMsg {
    ExecuteMsg::Settle {
        proof: f.proof.clone(),
        commitments: f.commitments.clone(),
        commitment_pok: f.commitment_pok.clone(),
        genesis_root: f.genesis_root,
        final_root: f.final_root,
        num_turns: f.num_turns,
        chain_digest: f.chain_digest,
    }
}

/// Instantiate a fresh settlement contract anchored at the fixture's own genesis
/// root, returning `(app, contract_addr, fixture)`.
fn setup() -> (App, Addr, Fixture) {
    let f = load_fixture();
    let mut app = App::default();
    let code = ContractWrapper::new(execute, instantiate, query);
    let code_id = app.store_code(Box::new(code));
    let sender = app.api().addr_make("deployer");

    let addr = app
        .instantiate_contract(
            code_id,
            sender,
            &InstantiateMsg {
                genesis_root: f.genesis_root,
                verifying_key_hash: "0x".to_string()
                    + &hex::encode(sha3_keccak(b"dregg-settlement-vk-dev-setup")),
            },
            &[],
            "dregg-settlement",
            None,
        )
        .expect("instantiate");
    (app, addr, f)
}

fn sha3_keccak(bytes: &[u8]) -> [u8; 32] {
    use sha3::{Digest, Keccak256};
    let d = Keccak256::digest(bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d);
    out
}

fn caller(app: &App) -> Addr {
    app.api().addr_make("relayer")
}

/// THE END-TO-END: the real Groth16 proof settles the real dregg root inside the
/// Cosmos runtime, advancing proven root + height.
#[test]
fn real_proof_settles_on_cosmos() {
    let (mut app, addr, f) = setup();
    let who = caller(&app);

    // Before: height 0, proven root == genesis anchor.
    let h0: HeightResponse = app
        .wrap()
        .query_wasm_smart(&addr, &cosmos_settlement::msg::QueryMsg::ProvenHeight {})
        .unwrap();
    assert_eq!(h0.height, 0);

    let res = app.execute_contract(who, addr.clone(), &settle_msg(&f), &[]);
    assert!(res.is_ok(), "real proof must settle: {res:?}");

    // After: height == num_turns, proven lanes == final root, root recorded.
    let h1: HeightResponse = app
        .wrap()
        .query_wasm_smart(&addr, &cosmos_settlement::msg::QueryMsg::ProvenHeight {})
        .unwrap();
    assert_eq!(h1.height, f.num_turns as u64);

    let lanes: LanesResponse = app
        .wrap()
        .query_wasm_smart(&addr, &cosmos_settlement::msg::QueryMsg::ProvenRootLanes {})
        .unwrap();
    assert_eq!(lanes.lanes, f.final_root);

    let root: RootResponse = app
        .wrap()
        .query_wasm_smart(&addr, &cosmos_settlement::msg::QueryMsg::ProvenRoot {})
        .unwrap();
    let proven: BoolResponse = app
        .wrap()
        .query_wasm_smart(
            &addr,
            &cosmos_settlement::msg::QueryMsg::IsProvenRoot {
                root: root.root.clone(),
            },
        )
        .unwrap();
    assert!(proven.value, "final root must be recorded as proven");
}

/// THE DECISIVE CANARY: the SAME real proof presented with a final root it does
/// not attest is REJECTED by the real pairing check, and nothing settles.
#[test]
fn real_proof_rejects_wrong_final_root() {
    let (mut app, addr, f) = setup();
    let who = caller(&app);

    let mut forged = f.final_root;
    forged[0] = forged[0].wrapping_add(1);
    let msg = ExecuteMsg::Settle {
        proof: f.proof.clone(),
        commitments: f.commitments.clone(),
        commitment_pok: f.commitment_pok.clone(),
        genesis_root: f.genesis_root,
        final_root: forged,
        num_turns: f.num_turns,
        chain_digest: f.chain_digest,
    };

    let res = app.execute_contract(who, addr.clone(), &msg, &[]);
    assert!(res.is_err(), "a forged final root must be rejected");

    // Nothing settled.
    let h: HeightResponse = app
        .wrap()
        .query_wasm_smart(&addr, &cosmos_settlement::msg::QueryMsg::ProvenHeight {})
        .unwrap();
    assert_eq!(h.height, 0);
}

/// A tampered proof point (A.x + 1) must be rejected — either as an off-curve
/// point or a failed pairing.
#[test]
fn real_proof_rejects_tampered_proof_point() {
    let (mut app, addr, f) = setup();
    let who = caller(&app);

    let mut proof = f.proof.clone();
    // Bump the low byte of A.x — flips it off the curve / off the statement.
    proof[0] = bump_hex(&proof[0]);
    let msg = ExecuteMsg::Settle {
        proof,
        commitments: f.commitments.clone(),
        commitment_pok: f.commitment_pok.clone(),
        genesis_root: f.genesis_root,
        final_root: f.final_root,
        num_turns: f.num_turns,
        chain_digest: f.chain_digest,
    };
    let res = app.execute_contract(who, addr, &msg, &[]);
    assert!(res.is_err(), "a tampered proof point must be rejected");
}

/// A tampered Pedersen commitment must be rejected by the commitment gate or the
/// (commitment-folded) pairing.
#[test]
fn real_proof_rejects_tampered_commitment() {
    let (mut app, addr, f) = setup();
    let who = caller(&app);

    let mut commitments = f.commitments.clone();
    commitments[0] = bump_hex(&commitments[0]);
    let msg = ExecuteMsg::Settle {
        proof: f.proof.clone(),
        commitments,
        commitment_pok: f.commitment_pok.clone(),
        genesis_root: f.genesis_root,
        final_root: f.final_root,
        num_turns: f.num_turns,
        chain_digest: f.chain_digest,
    };
    let res = app.execute_contract(who, addr, &msg, &[]);
    assert!(res.is_err(), "a tampered commitment must be rejected");
}

/// A settlement whose genesis lanes do not chain from the anchor fails continuity
/// (before any pairing work) — the anchor is pinned at instantiation.
#[test]
fn rejects_broken_continuity() {
    let (mut app, addr, f) = setup();
    let who = caller(&app);

    let mut forged_genesis = f.genesis_root;
    forged_genesis[3] = forged_genesis[3].wrapping_add(1);
    let msg = ExecuteMsg::Settle {
        proof: f.proof.clone(),
        commitments: f.commitments.clone(),
        commitment_pok: f.commitment_pok.clone(),
        genesis_root: forged_genesis,
        final_root: f.final_root,
        num_turns: f.num_turns,
        chain_digest: f.chain_digest,
    };
    let res = app.execute_contract(who, addr, &msg, &[]);
    assert!(res.is_err(), "broken continuity must be rejected");
}

/// Flip the last hex nibble of a `0x`-prefixed coordinate string.
fn bump_hex(s: &str) -> String {
    let mut chars: Vec<char> = s.chars().collect();
    let last = chars.len() - 1;
    let c = chars[last];
    let nc = match c {
        '0' => '1',
        'f' | 'F' => 'e',
        other => {
            let d = other.to_digit(16).unwrap();
            std::char::from_digit(d ^ 1, 16).unwrap()
        }
    };
    chars[last] = nc;
    chars.into_iter().collect()
}
