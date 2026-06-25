//! deos verified core on android — the STEP 1 smoke proof.
//!
//! Builds for `aarch64-linux-android`, runs on the live Android emulator (or a
//! Pixel) over `adb`. It constructs two sovereign cells, executes a REAL
//! `dregg-turn` transfer through the embedded `TurnExecutor`, and prints the
//! committed receipt — i.e. *the verified kernel commits a turn and a receipt
//! lands, on android, with zero source changes to the kernel.*
//!
//! This is the mobile analogue of "a turn commits, a receipt lands" — the same
//! executor the federation and the cockpit run, on an ARM64 Android device.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::{Turn, TurnResult},
};

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn transfer_turn(agent: CellId, from: CellId, to: CellId, nonce: u64, amount: u64) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: from,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer { from, to, amount }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn main() {
    println!("=== deos verified core :: android smoke ===");
    println!("target = {}", std::env::consts::ARCH);
    println!("os     = {}", std::env::consts::OS);

    // Two sovereign cells in a fresh ledger.
    let alice = make_open_cell(1, 1000);
    let bob = make_open_cell(2, 0);
    let alice_id = alice.id();
    let bob_id = bob.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(alice).expect("insert alice");
    ledger.insert_cell(bob).expect("insert bob");

    println!(
        "pre : alice={} bob={}",
        ledger.get(&alice_id).unwrap().state.balance(),
        ledger.get(&bob_id).unwrap().state.balance()
    );

    // Run a REAL transfer turn through the embedded verified executor.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = transfer_turn(alice_id, alice_id, bob_id, 0, 250);
    let result = executor.execute(&turn, &mut ledger);

    let receipt = match result {
        TurnResult::Committed { receipt, .. } => receipt,
        other => {
            eprintln!("FAIL: turn did not commit: {other:?}");
            std::process::exit(1);
        }
    };

    let alice_post = ledger.get(&alice_id).unwrap().state.balance();
    let bob_post = ledger.get(&bob_id).unwrap().state.balance();
    println!("post: alice={alice_post} bob={bob_post}");
    println!("receipt.turn_hash = {}", hex::encode(receipt.turn_hash));
    println!(
        "receipt.post_state_hash = {}",
        hex::encode(receipt.post_state_hash)
    );
    println!("receipt.computrons_used = {}", receipt.computrons_used);

    // Conservation + correctness: alice -250, bob +250, Σδ = 0.
    assert_eq!(alice_post, 750, "alice must be debited 250");
    assert_eq!(bob_post, 250, "bob must be credited 250");
    assert_eq!(
        alice_post + bob_post,
        1000,
        "value conserved (Sum-delta = 0)"
    );

    println!(
        "OK: the verified dregg kernel committed a transfer turn on android, conserved value, and emitted a receipt."
    );
}

// `hex` isn't a dep; inline a tiny encoder so the binary stays self-contained
// over just dregg-turn/dregg-cell/blake3.
mod hex {
    pub fn encode(bytes: impl AsRef<[u8]>) -> String {
        bytes.as_ref().iter().map(|b| format!("{b:02x}")).collect()
    }
}
