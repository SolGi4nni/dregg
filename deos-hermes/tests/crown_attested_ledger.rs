//! THE FULL FUSION — a jailed, attested brain turn, committed onto the verifiable ledger.
//!
//! `crown_attested_turn.rs` proves one confined-brain run is BOTH jailed (the OS-jail
//! teeth) AND attested (a `verify_zkoracle`-accepted `ZkOracleAttestation`). This test
//! closes the last leg: it BINDS that attestation into a genuine R2 kernel turn that
//! LANDS on a real `LocalNode`'s finalized ledger — so the on-ledger receipt now proves
//!
//! ```text
//!   jailed      — the confined-brain teeth (crown_attested_turn.rs);
//!   attested    — the zkOracle attestation of the turn (authentic ∧ well-formed ∧ inj-free);
//!   finalized   — committed as a real executor turn + landed on the node's finalized log;
//!   verifiable  — a light client re-verifies the chain AND recomputes the attestation
//!                 commitment to confirm the landed turn is bound to THIS attestation.
//! ```
//!
//! The chain is END-TO-END here: the attestation comes from a genuine
//! `run_hosted_agent_attested` jailed run (not a literal), its
//! `deos_hermes::attestation_commitment` is witnessed on the SAME metered turn the node
//! finalizes, and the binding is load-bearing — an unattested turn and a forged binding
//! are each distinguishable.
//!
//! Run: `cd deos-hermes && cargo test --test crown_attested_ledger`

#![cfg(unix)]

use std::io::Read;
use std::net::TcpListener;
use std::sync::{Arc, RwLock};

use agent_platform::{LocalNode, NodeMinter};
use deos_hermes::host::escape;
use deos_hermes::{
    AttestationCarrier, DreggHost, GrantRegistry, HermesGateway, attestation_commitment,
    verify_zkoracle,
};
use dregg_agent::agent::GrainTurnMinter;
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};
use dregg_zkoracle_prove::ZkOracleAttestation;
use grain_turn::ATTESTATION_SLOT;

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

fn default_gateway(rt: &AgentRuntime, root: HeldToken) -> HermesGateway<'_> {
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    HermesGateway::new(rt, root, registry)
}

fn spawn_listener() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind loopback listener");
    let port = listener.local_addr().unwrap().port();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            if let Ok(mut s) = stream {
                let mut buf = [0u8; 256];
                let _ = s.read(&mut buf);
            }
        }
    });
    port
}

/// A genuine jailed + attested confined-brain run → the confinement teeth AND the
/// turn's `ZkOracleAttestation`.
fn jailed_attested_run(carrier: &AttestationCarrier) -> ZkOracleAttestation {
    let kernel = ProcessKernel::new();
    let granted_port = spawn_listener();
    let sibling_port = spawn_listener();
    let (rt, root) = grantor();
    let host = DreggHost::new().with_egress_provider("127.0.0.1", granted_port);

    let report = host
        .run_hosted_agent_attested(
            &kernel,
            default_gateway(&rt, root),
            "search the docs, read the source, then run the build",
            Some(("127.0.0.1", granted_port)),
            Some(("127.0.0.1", sibling_port)),
            carrier,
        )
        .expect("a confined, attested hosted run");

    // The confinement teeth hold (the JAILED leg of the fusion).
    assert!(
        report.jailed,
        "the base jail holds; verdict=0x{:x}",
        report.verdict
    );
    assert_eq!(
        report.verdict & escape::ALL_NEUTRALIZED,
        escape::ALL_NEUTRALIZED,
        "execve / host-FS read / arbitrary socket each denied; verdict=0x{:x}",
        report.verdict
    );
    report
        .attestation
        .expect("the attested run carries a zkOracle attestation")
}

/// **THE FUSION — jailed → attested → committed → landed → verifiable.** A jailed,
/// attested brain turn's attestation is committed into a real R2 kernel turn that lands
/// on the node's finalized, light-client-verifiable ledger, bound to THIS attestation.
#[test]
fn attested_turn_lands_bound_to_its_attestation_and_is_verifiable() {
    let carrier = AttestationCarrier::default();

    // ── JAILED + ATTESTED — a genuine confined-brain run's attestation. ──
    let att = jailed_attested_run(&carrier);
    // The attestation itself verifies (authentic ∧ well-formed ∧ injection-free).
    verify_zkoracle(&att, carrier.config()).expect("the attestation verifies (all three legs)");
    let commitment = attestation_commitment(&att);

    // ── COMMITTED + LANDED — bind the attestation into a real R2 turn on a node. ──
    let node = LocalNode::new("crown.grain.dregg");
    let mut minter = NodeMinter::open(node.clone(), 8).expect("open node minter");
    minter.bind_attestation(commitment);
    // A genuine executor turn, committed onto the node's ledger AND landed on its
    // finalized receipt log (the same mint path the served platform drives).
    let turn_hash = minter
        .mint_turn("read-docs", 1, 1, [0u8; 32])
        .expect("the attested turn commits + lands");

    // ── VERIFIABLE — the light-client checks, plus the attestation binding. ──
    // (a) The node's finalized chain light-client-verifies, and the turn is on it.
    node.verify().expect("the node's finalized chain verifies");
    assert!(
        node.contains(&turn_hash),
        "the attested turn landed on the finalized log"
    );
    // (b) The committed turn cell (read off the real ledger) witnesses the commitment.
    assert_eq!(
        minter.attestation_slot(),
        Some(commitment),
        "the landed turn commits to the attestation"
    );
    assert_eq!(
        ATTESTATION_SLOT, 8,
        "the witnessed slot is the reserved attestation slot"
    );
    // (c) THE BINDING — a light client holding the attestation recomputes its commitment
    //     and confirms it equals the value the landed turn witnesses. This is what makes
    //     the receipt prove "driven by THIS attested brain," not merely "some hash."
    let recomputed = attestation_commitment(&att);
    assert_eq!(
        Some(recomputed),
        minter.attestation_slot(),
        "the recomputed attestation commitment matches the on-ledger witness"
    );
}

/// The binding is LOAD-BEARING — a forged binding (the ledger carries a hash that is NOT
/// the real attestation's commitment) and an UNATTESTED turn (no commitment) are each
/// DISTINGUISHABLE from a genuine attested turn. The green above is not a vacuous accept.
#[test]
fn forged_and_unattested_bindings_are_distinguishable() {
    let carrier = AttestationCarrier::default();
    let att = jailed_attested_run(&carrier);
    let real = attestation_commitment(&att);

    // (a) FORGED binding: the ledger commits to a DIFFERENT hash than the attestation's.
    let node = LocalNode::new("forged.grain.dregg");
    let mut forged = NodeMinter::open(node.clone(), 8).expect("open");
    forged.bind_attestation([0xEEu8; 32]); // not attestation_commitment(&att)
    forged
        .mint_turn("x", 1, 1, [0u8; 32])
        .expect("commits + lands");
    node.verify().expect("chain still verifies");
    // The landed slot does NOT equal the real attestation's commitment → a light client
    // recomputing from the attestation it holds REJECTS the binding.
    assert_ne!(
        forged.attestation_slot(),
        Some(real),
        "a forged binding does not match the attestation's recomputed commitment"
    );

    // (b) UNATTESTED turn: no commitment bound → the slot is not the attestation's hash.
    let bare_node = LocalNode::new("bare.grain.dregg");
    let mut bare = NodeMinter::open(bare_node.clone(), 8).expect("open");
    bare.mint_turn("y", 1, 1, [0u8; 32])
        .expect("commits + lands");
    bare_node.verify().expect("chain still verifies");
    assert_eq!(
        bare.bound_attestation(),
        None,
        "the bare minter bound no attestation"
    );
    assert_ne!(
        bare.attestation_slot(),
        Some(real),
        "an unattested turn carries no attestation binding (distinguishable)"
    );

    // (c) A TAMPERED attestation yields a DIFFERENT commitment — so a genuine on-ledger
    //     binding for the real attestation cannot be reused for a mutated one.
    let mut tampered = att.clone();
    let n = tampered.presentation.recv.len();
    tampered.presentation.recv[n - 3] ^= 0xFF;
    assert_ne!(
        attestation_commitment(&tampered),
        real,
        "a tampered attestation fingerprints differently — the commitment is total"
    );
}
