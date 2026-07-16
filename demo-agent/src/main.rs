//! Dregg End-to-End Demo: Token -> Signed Authorization -> Turn Execution
//!
//! Demonstrates the full integration between the two halves of the dregg system:
//!
//! **System A (execution):** cell -> turn -> coord (Mina-style call forests with capabilities)
//! **System B (presentation):** macaroon -> token -> commit (attenuable capability tokens)
//!
//! This demo shows the complete flow:
//! 1. A federation of 3 members is created (in-memory)
//! 2. An issuer mints a root macaroon token
//! 3. The token is attenuated (restricted to a specific service + time window)
//! 4. Cells are created in a Ledger (issuer, agent, target)
//! 5. Capabilities are granted from issuer to agent
//! 6. The agent signs the action authorizing the mutation (Ed25519)
//! 7. A Turn is submitted that carries the signature as authorization
//! 8. The executor verifies the signature and executes the turn
//! 9. A tampered signature is rejected (fail-closed)

use dregg_cell::{AuthRequired, CellId, Ledger, Permissions, cell::Cell};
use dregg_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};
use dregg_turn::builder::ActionBuilder;
use dregg_turn::{ComputronCosts, Effect, TurnBuilder, TurnExecutor, TurnResult};
use ed25519_dalek::{Signer, SigningKey};

// ─── Helpers ─────────────────────────────────────────────────────────────────

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!(
            "{:02x}{:02x}{:02x}{:02x}...",
            bytes[0], bytes[1], bytes[2], bytes[3]
        )
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

fn short_id(id: &CellId) -> String {
    short_hex(id.as_bytes())
}

fn agent_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("dregg-e2e-demo:{name}").as_bytes()).as_bytes()
}

fn demo_token_id() -> [u8; 32] {
    *blake3::hash(b"dregg-e2e-demo:token-domain").as_bytes()
}

fn section(step: usize, total: usize, title: &str) {
    println!();
    println!("  [{step}/{total}] {title}");
    println!("  {}", "-".repeat(50));
}

fn item(msg: &str) {
    println!("    {msg}");
}

// ─── Main ────────────────────────────────────────────────────────────────────

fn main() {
    println!();
    println!("  {}", "=".repeat(60));
    println!("  DREGG END-TO-END DEMO");
    println!("  Token -> Signed Authorization -> Turn Execution");
    println!("  {}", "=".repeat(60));

    let total_steps = 9;
    let token_id = demo_token_id();

    // ─── Step 1: Create a federation with 3 members ─────────────────────────

    section(1, total_steps, "Creating federation with 3 members");

    let issuer_key = agent_key("issuer-federation-member");
    let member2_key = agent_key("member-2");
    let member3_key = agent_key("member-3");

    // The agent's Ed25519 authorization keypair. The target cell will hold the
    // agent's verifying key, so a signature by the agent authorizes mutations.
    let agent_sk = SigningKey::from_bytes(&agent_key("agent-signing-key"));
    let agent_vk: [u8; 32] = agent_sk.verifying_key().to_bytes();

    item(&format!("Issuer key: {}", short_hex(&issuer_key)));
    item(&format!("Member 2 key: {}", short_hex(&member2_key)));
    item(&format!("Member 3 key: {}", short_hex(&member3_key)));
    item(&format!(
        "Agent authorization key (Ed25519): {}",
        short_hex(&agent_vk)
    ));

    // ─── Step 2: Mint a root macaroon token ─────────────────────────────────

    section(2, total_steps, "Minting root macaroon token");

    let root_token = MacaroonToken::mint(issuer_key, b"demo-kid-001", "dregg.fg-goose.online");
    item("Root token minted (unrestricted, full access)");
    item("  Location: dregg.fg-goose.online");
    item("  Key ID: demo-kid-001");

    // ─── Step 3: Attenuate the token ────────────────────────────────────────

    section(
        3,
        total_steps,
        "Attenuating token (restrict to service + time)",
    );

    let attenuation = Attenuation {
        services: vec![("compute".into(), "rw".into())],
        apps: vec![("agent-runtime".into(), "rw".into())],
        not_after: Some(2000000000), // Valid until ~2033
        ..Default::default()
    };

    let attenuated_token = root_token.attenuate(&attenuation).unwrap();
    item("Token attenuated with:");
    item("  - Service: compute (rw)");
    item("  - App: agent-runtime (rw)");
    item("  - Expires: 2000000000 (year ~2033)");

    // Verify the attenuated token still works for the intended request
    let test_request = AuthRequest {
        service: Some("compute".into()),
        app_id: Some("agent-runtime".into()),
        action: Some("rw".into()),
        now: Some(1700000000),
        ..Default::default()
    };
    let clearance = attenuated_token.verify(&test_request).unwrap();
    item(&format!(
        "  Verification: PASS (capabilities: {})",
        clearance.capabilities.len()
    ));

    // ─── Step 4: Create cells in a Ledger ───────────────────────────────────

    section(4, total_steps, "Creating cells in ledger");

    let mut ledger = Ledger::new();

    // Issuer cell: fully open (no auth required).
    let issuer_cell_key = agent_key("issuer-cell");
    let mut issuer_cell = Cell::with_balance(issuer_cell_key, token_id, 1_000_000);
    issuer_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let issuer_id = issuer_cell.id();
    ledger.insert_cell(issuer_cell).unwrap();

    // Agent cell: the actor that submits the turn.
    let agent_cell_key = agent_key("agent-cell");
    let mut agent_cell = Cell::with_balance(agent_cell_key, token_id, 100_000);
    agent_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let agent_id = agent_cell.id();
    ledger.insert_cell(agent_cell).unwrap();

    // Target cell: keyed to the agent's Ed25519 verifying key. With the default
    // user permissions, mutating its state requires a valid signature from that
    // key — so only the agent can authorize the mutation.
    let target_cell = Cell::with_balance(agent_vk, token_id, 50_000);
    let target_id = target_cell.id();
    ledger.insert_cell(target_cell).unwrap();

    item(&format!(
        "Issuer cell: {} (balance: 1,000,000)",
        short_id(&issuer_id)
    ));
    item(&format!(
        "Agent cell:  {} (balance: 100,000)",
        short_id(&agent_id)
    ));
    item(&format!(
        "Target cell: {} (balance: 50,000, requires SIGNATURE auth)",
        short_id(&target_id)
    ));

    // ─── Step 5: Grant capabilities ─────────────────────────────────────────

    section(5, total_steps, "Granting capabilities from issuer to agent");

    // Give agent access to the target cell
    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    item(&format!(
        "Agent granted capability to target cell {}",
        short_id(&target_id)
    ));

    // ─── Step 6: Prepare the authorization ──────────────────────────────────

    section(6, total_steps, "Agent signs the action (Ed25519)");

    // The federation binds the signature; the executor's default federation id
    // is the all-zero id, so the signer commits to that.
    let federation_id = [0u8; 32];
    let result_hash = *blake3::hash(b"computation_result:success:42").as_bytes();

    // Build the action once (unsigned placeholder) to derive its canonical
    // signing message, then sign that message with the agent's key.
    let unsigned_action = ActionBuilder::new(target_id, "execute_computation", agent_id)
        .signed_by([0u8; 64])
        .effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: result_hash,
        })
        .build();
    // Turn nonce 0: the turn below is built as `TurnBuilder::new(agent_id, 0)`
    // (the agent cell's first turn), and dregg-action-sig-v3 binds the
    // submitting turn's nonce into the signature.
    let signing_message =
        TurnExecutor::compute_signing_message(&unsigned_action, &federation_id, 0);
    let signature: [u8; 64] = agent_sk.sign(&signing_message).to_bytes();

    item("  Action: SetField(target, slot=0, computation_result)");
    item(&format!(
        "  Signing message: {}",
        short_hex(&signing_message)
    ));
    item(&format!(
        "  Ed25519 signature: {} (64 bytes)",
        short_hex(&signature)
    ));
    item("  The signature binds: target, method, effects, delegation, preconditions");

    // ─── Step 7: Submit a Turn with signed authorization ────────────────────

    section(7, total_steps, "Submitting Turn with signed authorization");

    let costs = ComputronCosts {
        action_base: 100,
        effect_base: 50,
        transfer: 75,
        create_cell: 500,
        proof_verify: 2000,
        signature_verify: 200,
        per_byte: 1,
    };
    let executor = TurnExecutor::new(costs);

    let mut turn_builder = TurnBuilder::new(agent_id, 0);
    turn_builder.set_fee(50000); // generous budget

    {
        let action = ActionBuilder::new(target_id, "execute_computation", agent_id)
            .signed_by(signature)
            .effect(Effect::SetField {
                cell: target_id,
                index: 0,
                value: result_hash,
            })
            .build();
        turn_builder.add_action(action);
    }

    let turn = turn_builder.build();
    item(&format!(
        "Turn built: agent {} -> target {}",
        short_id(&agent_id),
        short_id(&target_id)
    ));
    item("  Authorization: Ed25519 signature");
    item("  Effect: SetField(target, slot=0, computation_result)");

    // ─── Step 8: Execute and verify ─────────────────────────────────────────

    section(
        8,
        total_steps,
        "Executor verifies signature and executes turn",
    );

    let result = executor.execute(&turn, &mut ledger);

    match result {
        TurnResult::Committed {
            receipt,
            computrons_used,
            ..
        } => {
            item("TURN COMMITTED SUCCESSFULLY");
            item(&format!("  Computrons used: {computrons_used}"));
            item(&format!("  Turn hash: {}", short_hex(&receipt.turn_hash)));
            item(&format!(
                "  Effects hash: {}",
                short_hex(&receipt.effects_hash)
            ));
            item(&format!(
                "  Pre-state: {}",
                short_hex(&receipt.pre_state_hash)
            ));
            item(&format!(
                "  Post-state: {}",
                short_hex(&receipt.post_state_hash)
            ));

            // Verify the target cell's state was actually modified
            let target = ledger.get(&target_id).unwrap();
            let expected = *blake3::hash(b"computation_result:success:42").as_bytes();
            assert_eq!(
                target.state.fields[0], expected,
                "target state should be updated"
            );
            item("  Target cell state verified: field[0] contains computation result");
        }
        TurnResult::Rejected { reason, at_action } => {
            panic!("Turn rejected at action {at_action:?}: {reason}");
        }
        other => panic!("Unexpected turn result: {other:?}"),
    }

    // ─── Step 9: Demonstrate rejection with a tampered signature ─────────────

    section(
        9,
        total_steps,
        "Demonstrating rejection of a tampered signature",
    );

    // Flip a byte in the signature — it no longer verifies against the agent key.
    let mut bad_signature = signature;
    bad_signature[10] ^= 0xFF;

    let mut bad_turn_builder = TurnBuilder::new(agent_id, 1); // nonce=1 after first turn
    bad_turn_builder.set_fee(50000);
    // Chain from the first turn's receipt so the turn passes the receipt-chain
    // check and reaches authorization — the rejection is then genuinely due to
    // the tampered signature, not an incidental chain mismatch.
    if let Some(prev) = executor.get_last_receipt_hash(&agent_id) {
        bad_turn_builder.set_previous_receipt_hash(prev);
    }
    {
        let action = ActionBuilder::new(target_id, "evil_computation", agent_id)
            .signed_by(bad_signature)
            .effect(Effect::SetField {
                cell: target_id,
                index: 1,
                value: *blake3::hash(b"evil_result").as_bytes(),
            })
            .build();
        bad_turn_builder.add_action(action);
    }

    let bad_turn = bad_turn_builder.build();
    let bad_result = executor.execute(&bad_turn, &mut ledger);

    match bad_result {
        TurnResult::Rejected { reason, .. } => {
            item("TURN REJECTED (as expected)");
            item(&format!("  Reason: {reason}"));
            // Verify state was NOT modified
            let target = ledger.get(&target_id).unwrap();
            let expected_unchanged = *blake3::hash(b"computation_result:success:42").as_bytes();
            assert_eq!(target.state.fields[0], expected_unchanged);
            assert_eq!(target.state.fields[1], [0u8; 32]);
            item("  Target cell state unchanged: atomic rollback confirmed");
        }
        TurnResult::Committed { .. } => {
            panic!("Tampered signature should NOT have been accepted!");
        }
        other => panic!("Unexpected turn result: {other:?}"),
    }

    // ─── Summary ────────────────────────────────────────────────────────────

    println!();
    println!("  {}", "=".repeat(60));
    println!("  END-TO-END DEMO COMPLETE");
    println!("  {}", "=".repeat(60));
    println!();
    println!("  The full pipeline works:");
    println!("    1. Macaroon token minted and attenuated");
    println!("    2. Cells created and capabilities granted");
    println!("    3. Agent signed the action authorizing the mutation");
    println!("    4. Executor verified the Ed25519 signature against the cell key");
    println!("    5. Turn committed atomically (state updated)");
    println!("    6. Tampered signature correctly rejected (fail-closed)");
    println!();
    println!("  Security properties demonstrated:");
    println!("    [x] Authorization binding: signature covers the exact action + effects");
    println!("    [x] Soundness: tampered signatures are cryptographically rejected");
    println!("    [x] Fail-closed: no valid signature = always reject");
    println!("    [x] Atomic execution: rejected turns leave zero state changes");
    println!();
}
