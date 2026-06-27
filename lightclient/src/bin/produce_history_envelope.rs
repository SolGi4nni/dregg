//! `produce_history_envelope` — emit a REAL `ExternalHistoryEnvelope` JSON.
//!
//! The PRODUCER side of the whole-history light client, run NATIVELY (the expensive
//! recursive fold belongs off the verifier — a node/relayer runs it once). It folds
//! a real `k`-turn chain into ONE `WholeChainProof` and prints the versioned wire
//! envelope (the SAME shape the wasm `produce_external_history_envelope` emits, and
//! the SAME shape the wasm `verify_devnet_history` consumes), plus the config VK
//! anchor a verifier holds SEPARATELY.
//!
//! The browser light-client page bakes this output and verifies it in-tab
//! (`verify_devnet_history`) — re-witnessing nothing. The heavy fold is here; the
//! cheap verify is in the tab.
//!
//! Run: `cargo run -p dregg-lightclient --bin produce_history_envelope --features prover -- [k] [step]`

#![cfg(feature = "prover")]
#![forbid(unsafe_code)]

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_lightclient::fold_and_attest;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
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

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn make_turn(balance: u64, nonce: u32, amount: u64) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .expect("rotated transfer leg mints + self-verifies");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

fn make_chain(start_balance: u64, step: u64, k: usize) -> Vec<FinalizedTurn> {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    for i in 0..k {
        let nonce = i as u32;
        turns.push(make_turn(balance, nonce, step));
        balance -= step;
    }
    turns
}

/// Minimal standard base64 (with padding) — avoids adding a crate dep to this crate.
fn b64(bytes: &[u8]) -> String {
    const A: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = *chunk.get(1).unwrap_or(&0) as u32;
        let b2 = *chunk.get(2).unwrap_or(&0) as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(A[((n >> 18) & 63) as usize] as char);
        out.push(A[((n >> 12) & 63) as usize] as char);
        out.push(if chunk.len() > 1 {
            A[((n >> 6) & 63) as usize] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            A[(n & 63) as usize] as char
        } else {
            '='
        });
    }
    out
}

fn main() {
    let mut args = std::env::args().skip(1);
    let k: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(3);
    let step: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(7);

    eprintln!("producing a real {k}-turn whole-history aggregate (the heavy fold)…");
    let turns = make_chain(1_000, step, k);
    let (agg, _att) = fold_and_attest(&turns).expect("a continuous chain folds + light-verifies");

    let anchor_hex = agg.root_vk_fingerprint().to_hex();
    let proof_bytes_b64 = b64(&agg.to_bytes());
    let lanes_json = |a: &[dregg_circuit::field::BabyBear]| {
        a.iter()
            .map(|d| d.as_u32().to_string())
            .collect::<Vec<_>>()
            .join(",")
    };
    let genesis_json = lanes_json(&agg.genesis_root);
    let final_json = lanes_json(&agg.final_root);
    let genesis = agg.genesis_root[0].as_u32();
    let final_root = agg.final_root[0].as_u32();
    let chain_digest: Vec<u32> = agg.chain_digest.iter().map(|d| d.as_u32()).collect();
    let num_turns = agg.num_turns;
    let digest_json = chain_digest
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",");

    // The baked artifact: the wire envelope + the config anchor a verifier holds
    // SEPARATELY (same value here because the anchor is the circuit-shape fingerprint
    // an honest setup mints from a fold of this shape).
    println!("{{");
    println!("  \"anchor_hex\": \"{anchor_hex}\",");
    println!("  \"envelope\": {{");
    println!("    \"version\": 1,");
    println!("    \"vk_fingerprint_hex\": \"{anchor_hex}\",");
    println!("    \"proof_bytes_b64\": \"{proof_bytes_b64}\",");
    println!("    \"genesis_root\": [{genesis_json}],");
    println!("    \"final_root\": [{final_json}],");
    println!("    \"chain_digest\": [{digest_json}],");
    println!("    \"num_turns\": {num_turns}");
    println!("  }}");
    println!("}}");
    eprintln!("done: k={num_turns} genesis={genesis} final={final_root} anchor={anchor_hex}");
}
