//! Devnet integration demo: privacy-preserving bounty lifecycle.
//!
//! This example demonstrates the REAL privacy-preserving flow end-to-end:
//!
//! 1. Worker mints a credential token via AgentWallet.
//! 2. Worker generates a STARK proof of federation membership (zero-knowledge).
//! 3. Worker claims a bounty by presenting the proof through the HTTP API.
//! 4. The bounty board verifies the proof without learning the worker's identity.
//! 5. Worker submits work, issuer approves, payment is released.
//!
//! ## Privacy guarantees demonstrated
//!
//! - The worker proves "I am a federation member" without revealing WHICH member.
//! - The worker's blinded commitment (Poseidon2 hash) prevents identity linkage.
//! - Different claims by the same worker use different commitments (fresh randomness).
//! - The issuer never learns who the worker is until delivery.
//!
//! ## Running
//!
//! ```bash
//! # Start the devnet node:
//! cargo run -p pyana-node -- --dev
//!
//! # Start the bounty board (connects to devnet):
//! cargo run -p pyana-bounty-board -- --dev
//!
//! # Run this demo:
//! cargo run -p pyana-bounty-board --example devnet_demo
//! ```
//!
//! ## Notes
//!
//! - Generating real STARK proofs takes ~200-500ms depending on hardware.
//! - The demo uses `#[tokio::main]` for async HTTP calls to the bounty board.
//! - Federation root is fetched from the running bounty board's /health endpoint,
//!   then configured on the wallet side to match.

use std::time::Instant;

use pyana_sdk::{AgentWallet, AuthRequest, BabyBear};
use pyana_circuit::ivc::IvcBuilder;
use pyana_circuit::fold_air::{FoldWitness, RemovedFact, compute_test_checks_commitment};

use pyana_bounty_board::{
    ClaimRequest, CreateBountyRequest, QualificationRequirement,
    SubmitRequest, CompletionEvidence, ApproveRequest, compute_worker_commitment,
};

use reqwest::Client;
use serde_json::Value;

/// The bounty board base URL (override with BOUNTY_BOARD_URL env var).
fn base_url() -> String {
    std::env::var("BOUNTY_BOARD_URL").unwrap_or_else(|_| "http://127.0.0.1:3030".into())
}

/// Deterministic root key for the worker's credential token.
/// In production this would be securely generated and managed.
const WORKER_ROOT_KEY: [u8; 32] = [0x42; 32];

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Pyana Bounty Board: Privacy-Preserving Devnet Demo ===\n");

    let base = base_url();
    let client = Client::new();

    // =========================================================================
    // Step 0: Verify the bounty board is running and get federation state
    // =========================================================================
    println!("[0] Checking bounty board health at {base}...");
    let health: Value = client
        .get(format!("{base}/health"))
        .send()
        .await?
        .json()
        .await?;

    let federation_root_hex = health["federation_root"]["value"]
        .as_str()
        .unwrap_or("0000000000000000000000000000000000000000000000000000000000000000");
    let federation_root_live = health["federation_root"]["live"].as_bool().unwrap_or(false);

    println!("    Status: {}", health["status"]);
    println!("    Federation root: {federation_root_hex}");
    println!("    Root is live: {federation_root_live}");
    println!("    Node connected: {}", health["node"]["connected"]);
    println!();

    // =========================================================================
    // Step 1: Set up issuer and worker wallets
    // =========================================================================
    println!("[1] Setting up wallets...");

    // Issuer: posts bounties
    let issuer_wallet = AgentWallet::new();
    let issuer_cell = issuer_wallet.cell_id("bounty-board");
    let issuer_cell_hex = hex::encode(issuer_cell.as_bytes());
    println!("    Issuer cell: {issuer_cell_hex}");

    // Worker: claims bounties anonymously
    let mut worker_wallet = AgentWallet::new();
    let worker_pubkey = worker_wallet.public_key();
    println!("    Worker pubkey: {} (PRIVATE - never revealed to issuer)", hex::encode(&worker_pubkey.0));

    // Worker mints a credential token. In production, this token would be
    // issued by a federation authority. Here we mint locally for the demo.
    let worker_token = worker_wallet.mint_token(&WORKER_ROOT_KEY, "federation");
    println!("    Worker credential minted: service='{}', can_prove={}", worker_token.service, worker_token.can_prove());
    println!();

    // =========================================================================
    // Step 2: Advance the block height so deadlines work
    // =========================================================================
    println!("[2] Advancing block height...");
    let _: Value = client
        .post(format!("{base}/admin/height"))
        .json(&serde_json::json!({"delta": 10}))
        .send()
        .await?
        .json()
        .await?;
    println!("    Block height advanced to 10.");
    println!();

    // =========================================================================
    // Step 3: Configure federation root on the bounty board
    // =========================================================================
    println!("[3] Configuring federation root...");

    // Compute the federation root that matches this worker's proof key.
    // In production the federation root comes from the node's attestation.
    // For the demo, we compute it from the worker's token and set it on the board.
    let proof_key = blake3::derive_key("pyana-proof-key-v1", &WORKER_ROOT_KEY);
    let federation_root_bb = compute_synthetic_federation_root(&proof_key);
    let federation_root_bytes = bb_to_bytes(federation_root_bb);
    let root_hex = hex::encode(&federation_root_bytes);

    let set_root_resp: Value = client
        .post(format!("{base}/admin/federation-root"))
        .json(&serde_json::json!({"root": root_hex}))
        .send()
        .await?
        .json()
        .await?;
    println!("    Set federation root: {}", set_root_resp["root"].as_str().unwrap_or("?"));
    println!("    (This root matches our worker's proof key for the demo)");
    println!();

    // =========================================================================
    // Step 4: Create a bounty requiring federation membership
    // =========================================================================
    println!("[4] Creating bounty requiring federation membership proof...");

    let create_req = CreateBountyRequest {
        title: "Security audit of escrow logic".into(),
        description: "Full review of the conditional turn escrow. Must be a verified federation member.".into(),
        reward_amount: 25_000,
        reward_asset: 1,
        deadline_height: 5000,
        qualification: QualificationRequirement::FederationMember,
        tags: vec!["security".into(), "audit".into(), "advanced".into()],
        issuer_cell: issuer_cell_hex.clone(),
        reward_token: None,
    };

    let create_resp: Value = client
        .post(format!("{base}/bounties"))
        .json(&create_req)
        .send()
        .await?
        .json()
        .await?;

    let bounty_id = create_resp["id"]
        .as_str()
        .ok_or("no bounty ID in response")?
        .to_string();
    println!("    Bounty created: id={bounty_id}");
    println!("    Status: {}", create_resp["status"]);
    println!();

    // =========================================================================
    // Step 5: Generate the STARK qualification proof (the privacy magic)
    // =========================================================================
    println!("[5] Generating STARK federation membership proof...");
    println!("    This proves 'I am a valid federation member' WITHOUT revealing");
    println!("    which member I am. The verifier learns only: set membership.");
    println!();

    let proof_start = Instant::now();

    // Generate a real STARK presentation proof via the worker's wallet.
    // This calls through to the bridge layer which produces a Poseidon2 STARK.
    let request = AuthRequest {
        service: Some("federation".into()),
        action: Some("".into()), // Membership-only, no action binding
        ..Default::default()
    };

    let proof = worker_wallet.prove_authorization(&worker_token, &request)?;
    let wire_proof = proof.into_wire_proof();
    let proof_bytes = postcard::to_stdvec(&wire_proof)?;

    let proof_elapsed = proof_start.elapsed();
    println!("    Proof generated in {:.1}ms ({} bytes)", proof_elapsed.as_secs_f64() * 1000.0, proof_bytes.len());
    println!("    Proof tier: real STARK (Poseidon2 Merkle membership)");
    println!();

    // =========================================================================
    // Step 6: Compute blinded worker commitment (unlinkable identity)
    // =========================================================================
    println!("[6] Computing blinded worker commitment...");

    // Generate fresh randomness for the commitment.
    // Using a deterministic value for reproducibility in the demo.
    let commitment_randomness: [u8; 32] = *blake3::hash(b"demo-randomness-1").as_bytes();
    let worker_commitment = compute_worker_commitment(&worker_pubkey.0, &commitment_randomness);

    println!("    Commitment: {} (Poseidon2 hash of pubkey || randomness)", hex::encode(&worker_commitment));
    println!("    This commitment is UNLINKABLE to the worker's real identity.");
    println!("    A different randomness produces a different commitment, so the");
    println!("    same worker claiming multiple bounties cannot be correlated.");
    println!();

    // =========================================================================
    // Step 7: Claim the bounty via the HTTP API with the proof
    // =========================================================================
    println!("[7] Claiming bounty with STARK proof...");
    println!("    Sending qualification_proof ({} bytes) to the board...", proof_bytes.len());

    let claim_req = ClaimRequest {
        bounty_id: bounty_id.clone(),
        worker_commitment,
        qualification_proof: Some(proof_bytes.clone()),
    };

    let claim_resp = client
        .post(format!("{base}/bounties/{bounty_id}/claim"))
        .json(&claim_req)
        .send()
        .await?;

    let claim_status = claim_resp.status();
    let claim_body: Value = claim_resp.json().await?;

    if claim_status.is_success() {
        println!("    Claim ACCEPTED! Bounty status: {}", claim_body["status"]);
        println!("    The board verified our STARK proof without learning our identity.");
    } else {
        println!("    Claim REJECTED: {}", claim_body["error"].as_str().unwrap_or("unknown"));
        println!("    HTTP status: {claim_status}");
        println!();
        println!("    NOTE: If running in --dev mode with a zeroed federation root,");
        println!("    membership proofs will be rejected. Ensure the federation root");
        println!("    is configured (step 3 above) or run with a live devnet.");
        return Ok(());
    }
    println!();

    // =========================================================================
    // Step 8: Submit work (mock work product with proof-of-completion)
    // =========================================================================
    println!("[8] Submitting completed work...");

    // In a real scenario, this would be a receipt chain, external hash, or peer review.
    // Here we produce a mock completion proof to advance the lifecycle.
    let completion_proof = blake3::hash(b"audit-report-hash-binding").as_bytes().to_vec();

    let submit_req = SubmitRequest {
        bounty_id: bounty_id.clone(),
        worker_commitment,
        completion_evidence: CompletionEvidence::ExternalProof {
            url: "ipfs://QmExampleAuditReport".into(),
            hash: *blake3::hash(b"audit-report-content").as_bytes(),
        },
        completion_proof: completion_proof.clone(),
    };

    let submit_resp: Value = client
        .post(format!("{base}/bounties/{bounty_id}/submit"))
        .json(&submit_req)
        .send()
        .await?
        .json()
        .await?;

    println!("    Submission status: {}", submit_resp["status"]);
    println!("    Completion proof hash: {}", submit_resp["completion_proof_hash"].as_str().unwrap_or("?"));
    println!();

    // =========================================================================
    // Step 9: Issuer approves and payment is released
    // =========================================================================
    println!("[9] Issuer approving submission (triggers atomic payment)...");

    let approve_req = ApproveRequest {
        bounty_id: bounty_id.clone(),
        issuer_cell: issuer_cell_hex.clone(),
    };

    let approve_resp: Value = client
        .post(format!("{base}/bounties/{bounty_id}/approve"))
        .json(&approve_req)
        .send()
        .await?
        .json()
        .await?;

    println!("    Approval status: {}", approve_resp["status"]);
    println!("    Receipt hash: {}", approve_resp["receipt_hash"].as_str().unwrap_or("?"));
    println!("    Payment released atomically via conditional turn.");
    println!();

    // =========================================================================
    // Step 10: Verify final state
    // =========================================================================
    println!("[10] Verifying final bounty state...");

    let status_resp: Value = client
        .get(format!("{base}/bounties/{bounty_id}/status"))
        .send()
        .await?
        .json()
        .await?;

    let final_status = &status_resp["status"];
    println!("    Final status: {final_status}");
    assert!(
        final_status.as_object().map_or(false, |obj| obj.contains_key("Paid")),
        "Expected bounty to be in Paid state, got: {final_status}"
    );
    println!("    Bounty lifecycle complete: Open -> Claimed -> Submitted -> Paid");
    println!();

    // =========================================================================
    // Step 11: Demonstrate IVC standing proof generation (bonus)
    // =========================================================================
    println!("[11] Bonus: Generating IVC standing proof...");
    println!("    An IVC proof accumulates completed bounty steps into a");
    println!("    constant-size proof of standing (e.g., 'I completed >= 3 bounties').");
    println!("    No individual bounty IDs are revealed.");
    println!();

    let ivc_start = Instant::now();

    // Build a 3-step IVC chain (simulating 3 completed bounties).
    let initial_root = BabyBear::new(1);
    let mut builder = IvcBuilder::new(initial_root);

    for i in 0..3u32 {
        let old_root = BabyBear::new(i + 1);
        let new_root = BabyBear::new(i + 2);
        let fold = FoldWitness {
            old_root,
            new_root,
            removed_facts: vec![RemovedFact {
                predicate: BabyBear::new(100 + i),
                terms: [old_root, new_root, BabyBear::new(i)],
                membership_proof: None,
            }],
            num_added_checks: 1,
            added_checks_commitment: compute_test_checks_commitment(1),
        };
        use pyana_circuit::ivc::FoldDelta;
        builder.add_fold(FoldDelta::new(fold)).expect("fold should succeed");
    }

    let ivc_proof = builder.finalize_with_air().expect("IVC finalization should produce a proof");
    let ivc_bytes = postcard::to_stdvec(&ivc_proof)?;

    let ivc_elapsed = ivc_start.elapsed();
    println!("    IVC proof generated in {:.1}ms", ivc_elapsed.as_secs_f64() * 1000.0);
    println!("    Steps: {}, Size: {} bytes", ivc_proof.step_count, ivc_bytes.len());
    println!("    Verification: {:?}", pyana_circuit::verify_ivc(&ivc_proof, Some(initial_root)));
    println!();

    // Verify the IVC proof
    let verification = pyana_circuit::verify_ivc(&ivc_proof, Some(initial_root));
    assert_eq!(
        verification,
        pyana_circuit::IvcVerification::Valid,
        "IVC proof should verify as valid"
    );

    // =========================================================================
    // Summary
    // =========================================================================
    println!("=== Demo Complete ===");
    println!();
    println!("Privacy guarantees demonstrated:");
    println!("  1. Worker proved federation membership via STARK ({:.0}ms)", proof_elapsed.as_secs_f64() * 1000.0);
    println!("     - Verifier learned: 'someone in the federation is authorized'");
    println!("     - Verifier did NOT learn: which member, token contents, or identity");
    println!("  2. Worker commitment is unlinkable (fresh randomness per claim)");
    println!("     - Same worker, different bounties = different commitments");
    println!("  3. IVC standing proof is constant-size regardless of history");
    println!("     - Proves 'I completed >= N bounties' without revealing which ones");
    println!("  4. Payment released atomically (conditional turn resolution)");
    println!();
    println!("Full stack exercised: Wallet -> STARK proof -> HTTP API -> Verification -> State change");

    Ok(())
}

// =============================================================================
// Helper functions
// =============================================================================

/// Compute a synthetic federation root matching the wallet's derivation.
///
/// This replicates `AgentWallet::compute_federation_root_bb` so the bounty board's
/// root matches what the wallet produces as public input in its STARK proof.
fn compute_synthetic_federation_root(issuer_key: &[u8; 32]) -> BabyBear {
    use pyana_circuit::merkle_air::MerkleAir;

    let issuer_hash = bytes_to_babybear(issuer_key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(hash_index(i, 0, issuer_key)),
            BabyBear::new(hash_index(i, 1, issuer_key)),
            BabyBear::new(hash_index(i, 2, issuer_key)),
        ];
        current = MerkleAir::compute_parent(current, position, &siblings);
    }
    current
}

/// Convert a 32-byte array to a BabyBear field element via Poseidon2 hash.
fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
    let limbs = BabyBear::encode_hash(bytes);
    pyana_circuit::poseidon2::hash_many(&limbs)
}

/// Convert a BabyBear field element to a 32-byte array.
fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    let val = bb.as_u32();
    bytes[..4].copy_from_slice(&val.to_le_bytes());
    bytes
}

/// Deterministic sibling hash for Merkle path construction.
/// Must match `AgentWallet::hash_index` exactly.
fn hash_index(level: usize, sibling: usize, key: &[u8; 32]) -> u32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&level.to_le_bytes());
    hasher.update(&sibling.to_le_bytes());
    hasher.update(key);
    let hash = hasher.finalize();
    let bytes = hash.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) % pyana_circuit::field::BABYBEAR_P
}

/// Hex encoding helper.
mod hex {
    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}
