//! The DFA route-commitment relay wire, closed AT THE NODE.
//!
//! The `dregg-dfa-routing-v1` route-commitment-binding AIR
//! (`circuit/src/dsl/dfa_routing.rs`, faithful to the Lean model
//! `Dregg2.Crypto.DfaAcceptanceAir`) and its live verifier
//! (`turn::executor::membership_verifier::DslCircuitDfaVerifier`) both shipped —
//! but the node never MINTED the routing vk and never REGISTERED the verifier, so
//! a relay's `Witnessed { Dfa }` caveat was rejected before the verifier's own
//! logic could run (fail-closed / SAFE, but the built machinery was dead).
//!
//! `executor_setup` now mints [`route_circuit_vk`] (content-derived — no ceremony)
//! and `configure_turn_executor` deploys the routing program + registers the real
//! [`DslCircuitDfaVerifier`], so the same executor EVERY node ingress configures
//! (the thin-HTTP submit, the signed-envelope submit, the blocklace-finalized
//! path) dispatches a relay's Dfa caveat to the real STARK verifier.
//!
//! These teeth pin the WIRING closure through the `WitnessedPredicateRegistry`
//! entry a relay's caveat dispatches to:
//!
//! - the routing vk is minted, non-placeholder, and deployed in the node's Dfa
//!   registry;
//! - the node executor's `Dfa` kind now dispatches to the real `dsl-circuit-dfa`
//!   verifier (was a fail-closed stub / `KindNotRegistered`);
//! - a caveat whose commitment is not the deployed routing vk — including the
//!   relay-operator template's `[0u8; 32]` placeholder — FAILS CLOSED;
//! - malformed proof bytes under the deployed vk are REJECTED.
//!
//! The end-to-end honest-proof discharge (a valid route verifying through the
//! registered verifier) is `#[ignore]`d: it needs an honest STARK proof from the
//! routing prover, which is RED at HEAD independently of this wiring —
//! `dregg_circuit::dsl::dfa_routing::build_routing_witness`'s honest witness fails
//! the descriptor's own lowered constraints (`[#0, #11]` on row 0), panicking the
//! debug prover. The turn crate's own `live_routing_*` teeth are red with the
//! identical panic, and the circuit's prove/verify teeth were removed (only
//! `descriptor_is_deployable` remains) — a `circuit/src/dsl/dfa_routing.rs`
//! regression, not a node wiring gap. When that is repaired, drop the `#[ignore]`.

use std::collections::HashMap;
use std::sync::Arc;

use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
};
use dregg_circuit::BabyBear;
use dregg_circuit::dsl::dfa_routing::build_routing_witness;
use dregg_dsl_runtime::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, ProgramRegistry,
};
use dregg_node::executor_setup::{
    BlockHeightMode, canonical_router_transitions, configure_turn_executor,
    program_registry_with_route_circuit, route_circuit_vk,
};
use dregg_node::state::NodeState;
use dregg_turn::executor::prove_dfa_transition;
use dregg_turn::{ComputronCosts, TurnExecutor};

/// A node with its real on-disk state, and an executor configured exactly as
/// every node ingress configures it.
async fn configured_executor() -> (NodeState, TurnExecutor, tempfile::TempDir) {
    let dir = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(dir.path(), Vec::new()).expect("node state");
    let mut executor = TurnExecutor::new(ComputronCosts::default());
    {
        let s = state.read().await;
        configure_turn_executor(&mut executor, &s, BlockHeightMode::Current);
    }
    (state, executor, dir)
}

/// The vk is minted at all, it is content-derived (so every node agrees without a
/// ceremony or epoch decision), it is not the template's placeholder, and it is
/// deployed in the registry the node's Dfa verifier resolves against.
#[tokio::test]
async fn route_circuit_vk_is_deterministic_and_deployed() {
    let (state, _executor, _dir) = configured_executor().await;
    let s = state.read().await;
    assert_eq!(
        route_circuit_vk(),
        route_circuit_vk(),
        "the routing vk is content-derived, so it must be stable"
    );
    assert_ne!(
        route_circuit_vk(),
        [0u8; 32],
        "the routing vk must not be the relay-operator template's placeholder"
    );
    assert!(
        program_registry_with_route_circuit(&s).contains(&route_circuit_vk()),
        "the node's Dfa registry must carry the routing program at its vk"
    );
}

/// THE WIRING CLOSURE: the node-configured executor's `Dfa` kind now dispatches to
/// the real `dsl-circuit-dfa` verifier over a registry that carries the routing
/// program — no longer a fail-closed stub / `KindNotRegistered`. (The verifier
/// resolving the vk to the deployed program and running its STARK is exercised
/// end-to-end by `discharges_honest_route_end_to_end`, gated on the routing
/// prover; here we pin that the dispatch target is the real verifier, not a stub.)
#[tokio::test]
async fn node_executor_dispatches_dfa_to_the_real_verifier() {
    let (_state, executor, _dir) = configured_executor().await;
    let registry = executor
        .witnessed_registry
        .as_ref()
        .expect("the node executor carries a witnessed registry");
    let dfa = registry
        .get(WitnessedPredicateKind::Dfa)
        .expect("Dfa must be registered on the node executor (was KindNotRegistered)");
    assert_eq!(
        dfa.name(),
        "dsl-circuit-dfa",
        "Dfa must dispatch to the real DSL-circuit verifier, not a fail-closed stub"
    );
}

/// FAIL-CLOSED (undeployed commitment): a Dfa caveat whose commitment is NOT a
/// deployed vk is rejected — registering the verifier opened the routing circuit,
/// not the kind. The `[0u8; 32]` case is the relay-operator template's placeholder
/// commitment, which stays fail-closed until the template threads the vk through
/// (`dregg-storage-templates`). Uses synthetic proof bytes: the reject fires on
/// the missing-program lookup, before any STARK runs.
#[tokio::test]
async fn node_executor_fails_closed_on_undeployed_route_commitment() {
    let (_state, executor, _dir) = configured_executor().await;
    let registry = executor.witnessed_registry.as_ref().expect("registry");
    let sender = [7u8; 32];

    for (commitment, label) in [
        ([0u8; 32], "the relay-operator template's placeholder"),
        ([0xABu8; 32], "an attacker's self-declared circuit"),
    ] {
        let wp = WitnessedPredicate::dfa(commitment, InputRef::Sender, 0);
        let err = registry
            .verify(&wp, &PredicateInput::Sender(&sender), b"any-proof-bytes")
            .expect_err(&format!("{label} must fail closed"));
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "{label} must be REJECTED (an un-deployed circuit is never host-trusted); got {err:?}"
        );
    }
}

/// FAIL-CLOSED (malformed bytes at the deployed vk): garbage / empty proof bytes
/// under the real routing vk are rejected (the wire never decodes), not waved
/// through by the registration.
#[tokio::test]
async fn node_executor_rejects_malformed_route_proof() {
    let (_state, executor, _dir) = configured_executor().await;
    let registry = executor.witnessed_registry.as_ref().expect("registry");
    let sender = [7u8; 32];
    let wp = WitnessedPredicate::dfa(route_circuit_vk(), InputRef::Sender, 0);

    for bytes in [b"not-a-valid-dfa-wire".as_slice(), b"".as_slice()] {
        let err = registry
            .verify(&wp, &PredicateInput::Sender(&sender), bytes)
            .expect_err("a malformed routing proof must be rejected");
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "a malformed routing proof must be REJECTED; got {err:?}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE RELAY ATTACK: the open registry is not the verifier's registry.
// ─────────────────────────────────────────────────────────────────────────────

/// The attacker's TRIVIALLY-SATISFIABLE program — one boolean column, nothing
/// else. It constrains NOTHING about its 32 public inputs, so ANY public inputs
/// (i.e. any claimed route) admit an honest, verifying proof. This is what
/// anyone may push through `POST /programs/deploy`
/// (`api.rs::post_deploy_program`): the handler postcard-decodes an arbitrary
/// caller-supplied `CircuitDescriptor` and deploys it into `s.program_registry`
/// with no check on what the circuit says.
fn attacker_trivial_descriptor() -> CircuitDescriptor {
    CircuitDescriptor {
        name: "attacker-trivially-satisfiable-v1".to_string(),
        trace_width: 1,
        max_degree: 2,
        columns: vec![ColumnDef {
            name: "anything".to_string(),
            index: 0,
            kind: ColumnKind::Binary,
        }],
        // `col * (col - 1) == 0` — satisfied by an all-zero trace. Nothing binds
        // the public inputs, which is precisely the attacker's goal.
        constraints: vec![ConstraintExpr::Binary { col: 0 }],
        boundaries: vec![],
        public_input_count: 32,
        lookup_tables: vec![],
    }
}

/// Deploy the attacker's program into `s.program_registry` by EXACTLY the path
/// `post_deploy_program` uses: postcard-encode the descriptor (the wire the
/// handler accepts), decode it back, `CellProgram::new` (which computes the
/// vk_hash), and `s.program_registry.deploy`. Returns the attacker's vk_hash.
async fn deploy_foreign_program_as_the_open_endpoint_does(state: &NodeState) -> [u8; 32] {
    let descriptor_bytes =
        postcard::to_allocvec(&attacker_trivial_descriptor()).expect("descriptor serializes");
    // The handler's decode — an arbitrary caller-supplied descriptor off the wire.
    let descriptor: CircuitDescriptor =
        postcard::from_bytes(&descriptor_bytes).expect("the handler decodes it");
    let program = CellProgram::new(descriptor, 1);
    let mut s = state.write().await;
    s.program_registry
        .deploy(program)
        .expect("the open deploy endpoint accepts the attacker's descriptor")
}

/// An honest, genuinely-verifying proof for the attacker's own program, built by
/// the attacker in their OWN registry (the prover is a library — the attacker
/// runs it locally; nothing about proving is host-controlled).
fn attacker_honest_proof(vk_hash: &[u8; 32]) -> Vec<u8> {
    let mut attacker_registry = ProgramRegistry::new();
    let deployed = attacker_registry
        .deploy(CellProgram::new(attacker_trivial_descriptor(), 1))
        .expect("the attacker deploys their own program locally");
    assert_eq!(
        &deployed, vk_hash,
        "the vk_hash is content-derived, so the attacker's local copy has the SAME vk the node \
         registered — that is what makes the relay attack possible at all"
    );
    let mut witness = HashMap::new();
    witness.insert("anything".to_string(), vec![BabyBear::new(0); 2]);
    // 32 zero public inputs: the attacker's circuit binds none of them, so this
    // proof is honest for ANY claimed route.
    let public_inputs = vec![BabyBear::new(0); 32];
    prove_dfa_transition(&attacker_registry, vk_hash, &witness, 2, &public_inputs)
        .expect("the attacker's trivially-satisfiable program proves")
}

fn rejection_reason(err: &WitnessedPredicateError) -> String {
    match err {
        WitnessedPredicateError::Rejected { reason, .. } => reason.clone(),
        other => panic!("expected Rejected, got {other:?}"),
    }
}

/// THE TOOTH (the relay attack, refused).
///
/// `DslCircuitDfaVerifier` resolves ANY vk_hash present in the registry it is
/// handed and verifies THAT program's STARK against PROVER-SUPPLIED public
/// inputs. Nothing downstream pins the resolved program to the routing circuit.
/// So if the node handed the verifier `s.program_registry` — the OPEN registry
/// that the unauthenticated `POST /programs/deploy` lets anyone fill — an
/// attacker would: deploy a trivially-satisfiable circuit, prove it honestly
/// (trivially), and present a `Witnessed { Dfa }` caveat carrying THEIR vk. The
/// verifier would resolve it, the STARK would verify, and the caveat would
/// DISCHARGE — a router claiming a delivery it never made.
///
/// `program_registry_with_route_circuit` refuses this by construction: it builds
/// a FRESH registry holding EXACTLY the canonical route circuit, so the
/// attacker's vk is not resolvable at all and the caveat fails closed at the
/// lookup — WHILE the canonical route vk still resolves to its program.
///
/// This test goes RED if anyone reverts that function to `s.program_registry.clone()`.
#[tokio::test]
async fn foreign_deployed_program_cannot_discharge_a_dfa_caveat() {
    let dir = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(dir.path(), Vec::new()).expect("node state");

    // (a) The attacker fills the node's OPEN registry, exactly as the endpoint
    // does — BEFORE the executor is configured. The ordering is load-bearing and
    // faithful to the node: every ingress builds a FRESH executor per turn
    // (`new_submit_executor` / `new_verify_executor` → `configure_turn_executor`),
    // so the Dfa verifier's registry is snapshotted at TURN time — after any
    // `POST /programs/deploy` the attacker has already made. Configuring the
    // executor first would make this test pass for the wrong reason (a stale
    // pre-attack snapshot) rather than because of the pinning.
    let attacker_vk = deploy_foreign_program_as_the_open_endpoint_does(&state).await;

    let mut executor = TurnExecutor::new(ComputronCosts::default());
    {
        let s = state.read().await;
        configure_turn_executor(&mut executor, &s, BlockHeightMode::Current);
        assert!(
            s.program_registry.contains(&attacker_vk),
            "the open deploy surface is REAL: the attacker's circuit is in s.program_registry \
             (this is the registry that must NOT reach the Dfa verifier)"
        );
        assert_ne!(
            attacker_vk,
            route_circuit_vk(),
            "the attacker's circuit is a different program than the canonical route circuit"
        );
        assert!(
            !program_registry_with_route_circuit(&s).contains(&attacker_vk),
            "the Dfa verifier's registry must NOT carry a program deployed through the open \
             endpoint — it holds EXACTLY the canonical route circuit"
        );
    }

    // The attacker's proof is genuinely valid — it verifies against a verifier
    // built over the attacker's own registry. So the refusal below is the PINNED
    // REGISTRY talking, not a bad proof.
    let proof = attacker_honest_proof(&attacker_vk);
    {
        use dregg_cell::predicate::WitnessedPredicateVerifier;
        use dregg_turn::executor::DslCircuitDfaVerifier;
        let mut open = ProgramRegistry::new();
        open.deploy(CellProgram::new(attacker_trivial_descriptor(), 1))
            .expect("deploy");
        let attacker_verifier = DslCircuitDfaVerifier::new(Arc::new(open));
        attacker_verifier
            .verify(&attacker_vk, &PredicateInput::Sender(&[7u8; 32]), &proof)
            .expect(
                "the attacker's proof is HONEST for their own circuit — an open registry WOULD \
                 discharge it, which is exactly the hole being closed",
            );
    }

    // (b) THE REFUSAL: the node-configured executor rejects the caveat, and the
    // rejection is the REGISTRY LOOKUP failing closed — the attacker's circuit is
    // not host-trusted, so its STARK is never even reached.
    let registry = executor.witnessed_registry.as_ref().expect("registry");
    let wp = WitnessedPredicate::dfa(attacker_vk, InputRef::Sender, 0);
    let err = registry
        .verify(&wp, &PredicateInput::Sender(&[7u8; 32]), &proof)
        .expect_err(
            "a Dfa caveat carrying a program deployed through the open POST /programs/deploy must \
             be REFUSED — the node's Dfa verifier resolves ONLY the canonical route circuit",
        );
    let reason = rejection_reason(&err);
    assert!(
        reason.contains("no DSL program registered"),
        "the refusal must be the pinned registry failing the lookup closed (the attacker's \
         circuit is not host-trusted); got: {reason}"
    );

    // (c) The canonical route vk STILL RESOLVES: the same bytes under the route
    // vk get PAST the lookup and die in the route circuit's own verification —
    // proving the pinning refused the foreign program without deafening the
    // deployed one.
    let wp_route = WitnessedPredicate::dfa(route_circuit_vk(), InputRef::Sender, 0);
    let route_err = registry
        .verify(&wp_route, &PredicateInput::Sender(&[7u8; 32]), &proof)
        .expect_err("a proof for the attacker's circuit is not a proof for the route circuit");
    let route_reason = rejection_reason(&route_err);
    assert!(
        !route_reason.contains("no DSL program registered"),
        "the CANONICAL route vk must still RESOLVE to its deployed program (rejection must come \
         from the route circuit's own verification, not a missing registration); got: \
         {route_reason}"
    );
}

/// END-TO-END DISCHARGE (blocked on the routing prover, see module docs): an
/// honest route verifies through the registered verifier at the deployed vk. This
/// needs an honest STARK proof, and `build_routing_witness` fails the descriptor's
/// own lowered constraints at HEAD (`circuit/src/dsl/dfa_routing.rs` regression),
/// panicking the debug prover. Drop the `#[ignore]` once that is repaired.
#[ignore = "blocked on circuit/src/dsl/dfa_routing.rs: honest witness fails its own \
            lowered constraints [#0,#11] on row 0 (turn's live_routing_* red identically)"]
#[tokio::test]
async fn discharges_honest_route_end_to_end() {
    let (state, executor, _dir) = configured_executor().await;
    let transitions = canonical_router_transitions();
    let wire = {
        let s = state.read().await;
        let programs = program_registry_with_route_circuit(&s);
        let (witness, public_inputs) = build_routing_witness(&transitions, 0, &[0, 1, 0])
            .expect("the canonical router accepts internal,external,internal");
        let num_rows = witness.get("current_state").map(|v| v.len()).unwrap();
        prove_dfa_transition(
            &programs,
            &route_circuit_vk(),
            &witness,
            num_rows,
            &public_inputs,
        )
        .expect("the routing proof wire builds against the node-deployed program")
    };

    let registry = executor.witnessed_registry.as_ref().expect("registry");
    let wp = WitnessedPredicate::dfa(route_circuit_vk(), InputRef::Sender, 0);
    let sender = [7u8; 32];
    registry
        .verify(&wp, &PredicateInput::Sender(&sender), &wire)
        .expect("an honest route must discharge the relay's Dfa caveat at the deployed vk");
}
