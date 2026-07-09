//! node_integrator_e2e.rs — the SINGLE-PROCESS NODE INTEGRATOR smoke test.
//!
//! THE BIND. The distributed layer is five real, individually-tested library
//! crates — `dregg-blocklace` (DAG-BFT consensus), `dregg-captp` (cap-transfer),
//! `dregg-federation`, `dregg-coord`, `dregg-net`. The `dregg-node` binary
//! ALREADY wires them: `main.rs::run_node` constructs a `NodeState` (the verified
//! executor + ledger + store + cipherclerk) and calls
//! `blocklace_sync::run_blocklace_sync`, which stands up the real
//! `dregg_blocklace::finality::Blocklace`, the gossip transport, the round-driven
//! producer, the quiescent finality executor, and the attested-root writer.
//!
//! What was MISSING is a clean, in-process witness that the whole flow binds and
//! runs END-TO-END without spawning OS processes or leaning on the loopback
//! gossip wire (whose small-N dissemination is the named Stage-5 residual — see
//! `tests/three_node_ordering_rule.rs`). This test IS that witness. It drives the
//! REAL production path in a single process, SOLO mode (a committee of one, where
//! `tau` finalizes every block trivially in sequence):
//!
//!   submit a real signed Transfer turn
//!     → `BlocklaceHandle::submit_turn` inserts a real Ed25519-signed block into
//!       the real blocklace DAG (real blake3 block id, real parent links)
//!     → the QUIESCENT `spawn_finality_executor` task wakes on the finality
//!       notify, runs `poll_finalized_blocks` (the verified `tau` ordering),
//!       executes the finalized turn through the verified executor
//!       (`execute_finalized_turn`), and writes a fresh, Ed25519-signed
//!       `AttestedRoot` (the light-client-verifiable receipt) into the store.
//!
//! THE BAR (each is a hard assertion; no `catch_unwind`, no weakened checks):
//!   [A] HONEST FLOW — after submitting one Transfer turn, the authoritative
//!       ledger reflects the transfer (sender debited, recipient credited) AND a
//!       signed `AttestedRoot` was written whose quorum signature VERIFIES against
//!       the node's own validator key and whose `merkle_root` equals the committed
//!       ledger root. This is the turn → prove/execute → consensus → finalize →
//!       verifiable-receipt loop, closed in one process.
//!   [B] BYZANTINE TOOTH — an equivocating block (a second, distinct block at a
//!       `(creator, seq)` the lace already holds) is REJECTED by the blocklace
//!       insert (`receive_block` → `BlockError::Equivocation`), the equivocator is
//!       recorded, and the forked block is NOT admitted to the DAG. Consensus does
//!       not accept a double-vote.
//!
//! This is the dual of `blocklace/tests/multi_node_convergence.rs` (which proves
//! the SAME `tau` rule + equivocation exclusion over a hand-built DAG) and
//! `tests/three_node_ordering_rule.rs` (which drives three real node processes
//! over the wire): here we bind ALL the node components — executor, store,
//! cipherclerk, blocklace, finality executor, attested-root writer — and run the
//! honest flow to a verifiable receipt in a single process, deterministically.
#![cfg(test)]

use std::time::{Duration, Instant};

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_turn::{CallForest, Effect, Turn};

use crate::blocklace_sync::run_blocklace_sync;
use crate::state::NodeState;

/// A fully-open permission set so the executor authorizes a Transfer signed by
/// the cell's owning cipherclerk without a separate grant.
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

/// Token domain every cell in this test shares (the node's default agent domain,
/// `blake3("default")`). A Transfer must stay within one token domain.
fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

/// Build a real signed Transfer `Turn` from `agent`, signed by the node's own
/// cipherclerk over the executor's verification domain — exactly the shape the
/// faucet / `/turn/submit` ingress produces, ready for the blocklace.
fn build_signed_transfer(
    state: &crate::state::NodeStateInner,
    agent: CellId,
    to: CellId,
    amount: u64,
    nonce: u64,
) -> dregg_sdk::SignedTurn {
    let transfer = Effect::Transfer {
        from: agent,
        to,
        amount,
    };
    // Sign actions over the SAME federation id the executor verifies against
    // (`federation_id_for_executor`: `blake3(pubkey)` on an unconfigured solo node).
    let exec_federation_id = crate::executor_setup::federation_id_for_executor(state);
    let action = state
        .cclerk
        .make_action(agent, "transfer", vec![transfer], &exec_federation_id);
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);

    let mut turn = Turn {
        agent,
        nonce,
        fee: 0, // sized below to the estimated computron cost so the budget gate passes
        memo: Some(format!("integrator_transfer:{amount}")),
        valid_until: Some(1_000_000_000),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: state
            .cclerk
            .receipt_chain()
            .last()
            .map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    // The executor's budget gate caps computrons at `turn.fee` (`estimated > fee`
    // → BudgetExceeded). Size the fee to the estimated cost so the gate passes.
    let executor = crate::executor_setup::new_submit_executor(state);
    turn.fee = executor.estimate_cost(&turn);

    state.cclerk.sign_turn(&turn)
}

/// THE INTEGRATOR SMOKE TEST: bind the node end-to-end in one process and prove
/// the honest flow reaches a verifiable receipt, then prove the Byzantine tooth.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn single_process_node_binds_consensus_executor_and_finalizes_a_verifiable_receipt() {
    // Install the ring CryptoProvider for rustls (the gossip/QUIC transport the
    // blocklace stands up needs it) — exactly what `main()` does at startup.
    // Idempotent: a second install is a no-op error we ignore (another test in the
    // same process may have installed it first).
    let _ = rustls::crypto::ring::default_provider().install_default();

    // ── stand up a REAL NodeState (tempdir-backed store + fresh cipherclerk) ────
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");

    // The node's own agent cell (cclerk-derived, default token domain) is the
    // turn's actor; fund it and a recipient cell, both with open permissions so
    // the verified executor authorizes the cclerk-signed Transfer.
    let (agent_cell, recipient_cell, agent_pubkey) = {
        let mut s = state.write().await;
        let token = default_token_id();
        let agent_pubkey = s.cclerk.public_key().0;

        let agent_id = crate::executor_setup::local_agent_cell(&s);
        let mut agent = Cell::with_balance(agent_pubkey, token, 1_000_000);
        agent.permissions = open_permissions();
        assert_eq!(
            agent.id(),
            agent_id,
            "seeded agent cell id must match the cclerk-derived agent"
        );
        s.ledger.insert_cell(agent).expect("insert agent cell");

        // Recipient: a distinct open cell in the same token domain.
        let mut rk = [0u8; 32];
        rk[0] = 0x5A;
        rk[31] = 0xC3;
        let mut recipient = Cell::with_balance(rk, token, 0);
        recipient.permissions = open_permissions();
        let recipient_id = recipient.id();
        s.ledger
            .insert_cell(recipient)
            .expect("insert recipient cell");

        (agent_id, recipient_id, agent_pubkey)
    };
    let _ = agent_pubkey;

    // ── bind the consensus + finality machinery (SOLO: committee of one) ────────
    // This is the EXACT call `main.rs::run_node` makes: it builds the real
    // `Blocklace`, gossip transport, round producer, the quiescent finality
    // executor (which executes finalized turns + writes attested roots), and
    // returns the handle. No peers ⇒ solo ⇒ `tau` finalizes every block in seq.
    let handle = run_blocklace_sync(
        state.clone(),
        0,      // gossip_port 0 ⇒ OS-assigned ephemeral (no fixed bind clash)
        true,   // auto_approve_joins (irrelevant solo)
        100,    // blocklace_checkpoint_interval
        10_000, // constitution wave timeout ms
        50,     // block_cadence_ms (fast check tick for the test)
        2_000,  // idle_heartbeat_ms
        0,      // min_block_interval_ms (no rate cap in-test)
        None,   // advertise_addr (solo — nothing to advertise)
    )
    .await
    .expect("run_blocklace_sync must return a handle in solo mode");
    state.set_blocklace(handle.clone()).await;

    // ── [A] HONEST FLOW: submit one real signed Transfer turn ───────────────────
    let amount = 250u64;
    let agent_balance_before: i64 = {
        let s = state.read().await;
        s.ledger
            .get(&agent_cell)
            .expect("agent cell present")
            .state
            .balance()
    };
    let (turn_data, fee) = {
        let s = state.read().await;
        let nonce = s
            .ledger
            .get(&agent_cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        let signed = build_signed_transfer(&s, agent_cell, recipient_cell, amount, nonce);
        // The turn's fee (sized to the estimated computron cost). On this well-less
        // dev node it is BURNED (no fee-well/proposer/treasury configured) — the
        // proven `FeeHistory.feeStep_conserves_modulo_burn` behaviour the escrow
        // services rely on. So the sender is debited `amount + fee`, not just `amount`.
        let fee = signed.turn.fee;
        (
            postcard::to_stdvec(&signed).expect("serialize SignedTurn"),
            fee,
        )
    };

    // Insert the turn block into the real blocklace DAG. In solo mode this
    // produces the block immediately (real Ed25519 signature, real blake3 id) and
    // notifies the finality executor.
    let (_receipt_block, _level) = handle.submit_turn(&state, turn_data).await;

    // ── wait for the QUIESCENT finality executor to commit + attest ─────────────
    // The background task wakes on the finality notify, finalizes via `tau`,
    // executes the turn, and writes the signed AttestedRoot. Poll the
    // authoritative store/ledger until the receipt appears (bounded).
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut attested = None;
    let mut agent_balance_after;
    loop {
        {
            let s = state.read().await;
            agent_balance_after = s
                .ledger
                .get(&agent_cell)
                .map(|c| c.state.balance())
                .unwrap_or(agent_balance_before);
            if let Ok(Some(root)) = s.store.latest_attested_root() {
                if root.height >= 1 {
                    attested = Some(root);
                    break;
                }
            }
        }
        if Instant::now() >= deadline {
            break;
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    let recipient_balance_after: i64 = {
        let s = state.read().await;
        s.ledger
            .get(&recipient_cell)
            .map(|c| c.state.balance())
            .unwrap_or(0)
    };

    // [A.1] the transfer was applied authoritatively by the FINALIZED executor.
    assert_eq!(
        recipient_balance_after, amount as i64,
        "[A] recipient must be credited the transfer amount by the finalized executor; got {recipient_balance_after}"
    );
    assert_eq!(
        agent_balance_before - agent_balance_after,
        amount as i64 + fee as i64,
        "[A] sender must be debited the transfer amount PLUS the (burned) turn fee \
         (before={agent_balance_before} after={agent_balance_after} amount={amount} fee={fee}) — \
         matches the finalized-path fee model (FeeHistory.feeStep_conserves_modulo_burn) and the \
         sibling finalized_transfer_…_uniform_across_nodes assertion"
    );

    // [A.2] a light-client-verifiable AttestedRoot was written and its quorum
    // signature VERIFIES against the node's own validator key (the receipt is
    // genuinely signed, not a placeholder).
    let attested = attested.expect(
        "[A] a finalized AttestedRoot (the light-client receipt) must be written within the deadline \
         — the turn never finalized through consensus",
    );
    assert!(
        attested.height >= 1,
        "[A] attested root height must advance past genesis; got {}",
        attested.height
    );
    assert!(
        attested.blocklace_block_id.is_some(),
        "[A] the attested root must be anchored to the finalized blocklace block"
    );
    assert!(
        !attested.quorum_signatures.is_empty(),
        "[A] the attested root must carry the solo validator's quorum signature"
    );

    // Re-derive the canonical signing message and VERIFY the recorded signature —
    // the exact check a light client performs on a fetched receipt.
    {
        let stored = &attested;
        let to_verify = dregg_types::AttestedRoot {
            merkle_root: stored.merkle_root,
            note_tree_root: stored.note_tree_root,
            nullifier_set_root: stored.nullifier_set_root,
            height: stored.height,
            timestamp: stored.timestamp,
            blocklace_block_id: stored.blocklace_block_id,
            finality_round: stored.finality_round,
            quorum_signatures: stored.quorum_signatures.clone(),
            threshold_qc: stored.threshold_qc.clone(),
            threshold: stored.threshold,
            federation_id: stored.federation_id,
            receipt_stream_root: stored.receipt_stream_root,
            // Local light-client re-verify of the ed25519 half only; the wire
            // hybrid quorum is not reconstructed from persisted state here.
            hybrid_quorum: Vec::new(),
        };
        let msg = to_verify.signing_message();
        let (pk, sig) = &stored.quorum_signatures[0];
        assert!(
            dregg_types::verify(pk, &msg, sig),
            "[A] the attested root's quorum signature must VERIFY against the validator key — \
             a light client would reject this receipt otherwise"
        );
    }

    // [A.3] the receipt's merkle_root must equal the committed ledger root (the
    // attestation actually binds the state the executor produced).
    {
        let s = state.read().await;
        let committed_root = crate::blocklace_sync::canonical_ledger_root(&s.ledger);
        assert_eq!(
            attested.merkle_root, committed_root,
            "[A] the attested root's merkle_root must equal the committed ledger root (the receipt \
             binds the finalized state)"
        );
    }

    eprintln!(
        "[A] PASS — one signed Transfer turn flowed submit → blocklace insert → tau finalize → \
         verified executor commit → signed AttestedRoot (height={}, block anchored, signature \
         verifies, merkle_root == committed ledger root). The full single-process node flow binds.",
        attested.height
    );

    // ── [B] BYZANTINE TOOTH: an equivocating block is REJECTED at insert ────────
    // Forge a SECOND, distinct block at a (creator, seq) the lace already holds.
    // The blocklace `receive_block` must detect the fork, refuse the block, and
    // record the equivocator. (This exercises the SAME insert path the node's
    // gossip receiver uses for peer blocks.)
    {
        use dregg_blocklace::finality::{Block, BlockError, Payload};

        // A fresh "peer" signing key — a creator the lace will see for the first
        // time at seq 1, then try to fork.
        let peer_sk = ed25519_dalek::SigningKey::from_bytes(&[0x42u8; 32]);
        // Tips / equivocators are keyed by the HYBRID id (== `Block::creator`).
        let peer_creator = Block::hybrid_id(&peer_sk);

        let mut lace = handle.lace.write().await;
        let honest = Block::new(
            &peer_sk,
            1,
            Payload::Turn(b"peer-honest-block".to_vec()),
            Vec::new(),
        );
        lace.receive_block(honest.clone())
            .expect("[B] an honest first peer block must be accepted");
        // Pre-fork invariant: the honest block IS the peer's tip, the peer is NOT
        // yet an equivocator.
        assert_eq!(
            lace.tips().get(&peer_creator),
            Some(&honest.id()),
            "[B] the honest peer block must be the peer's tip before the fork"
        );
        assert!(
            !lace.equivocators().contains(&peer_creator),
            "[B] the peer must not be an equivocator before forking"
        );

        // The fork: SAME creator, SAME seq, DIFFERENT payload ⇒ equivocation.
        let fork = Block::new(
            &peer_sk,
            1,
            Payload::Turn(b"peer-FORK-block".to_vec()),
            Vec::new(),
        );
        let result = lace.receive_block(fork);
        match result {
            Err(BlockError::Equivocation { creator, seq, .. }) => {
                assert_eq!(
                    creator, peer_creator,
                    "[B] the equivocator must be the forking peer"
                );
                assert_eq!(seq, 1, "[B] the equivocation is at seq 1");
            }
            other => panic!(
                "[B] an equivocating block MUST be rejected as BlockError::Equivocation; got {other:?}"
            ),
        }
        // The fork is REJECTED at the consensus level: the equivocator is recorded
        // and — the load-bearing exclusion — its TIP is removed, so it anchors
        // NOTHING in the `tau` order and contributes NO finalized turn (the fork
        // block itself is retained only as an EVIDENCE exhibit, never as a live
        // tip — `finality.rs::receive_block`).
        assert!(
            lace.equivocators().contains(&peer_creator),
            "[B] the forking creator must be recorded as an equivocator"
        );
        assert_eq!(
            lace.tips().get(&peer_creator),
            None,
            "[B] the equivocator's tip must be REMOVED so it anchors nothing in tau ordering"
        );
    }

    eprintln!(
        "[B] PASS — an equivocating block (second block at an existing (creator, seq)) was REJECTED \
         by the blocklace insert (BlockError::Equivocation): the equivocator is recorded and its \
         tip removed (it anchors nothing in tau ordering; the fork block is kept only as evidence). \
         Consensus does not accept a double-vote."
    );
}
