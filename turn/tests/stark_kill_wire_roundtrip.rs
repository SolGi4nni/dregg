//! # Gate-3 RUNTIME round-trip for the `StarkProof` → `Ir2BatchProof` wire migration.
//!
//! The migration's premise: the proof-witness blob at the executor/bridge seam is an OPAQUE
//! `Vec<u8>`, so `cargo build` cannot see the byte-format flip (`postcard(StarkProof)` →
//! `postcard(Ir2BatchProof)`) nor the air-name dispatch. A build-green edit can still fail at
//! RUNTIME. This test is the gate the build cannot provide: it drives the exact CONSUMER contract
//! the migration installs, through the REAL prover/verifier (never a mock), per predicate kind.
//!
//! The contract, end to end:
//!   1. PRODUCER: build an HONEST witness for the descriptor and prove it with the deployed
//!      [`prove_vm_descriptor2`] → an [`Ir2BatchProof`].
//!   2. WIRE: `postcard`-encode the proof into the blob table (the NEW format). The blob carries
//!      NO air-name — that is the scout design point: the descriptor is chosen from the PREDICATE's
//!      own identity, NOT from prover-controlled proof bytes.
//!   3. CONSUMER: from the predicate identity (kind/name → descriptor) run
//!      [`descriptor_by_name`] (fail-closed [`None`] on a miss), decode the blob, and check it with
//!      the deployed [`verify_vm_descriptor2`].
//!
//! Every kind is NON-VACUOUS: the honest witness is ACCEPTED, and each of a forged public input,
//! a tampered blob, a cross-kind descriptor, and a fail-closed dispatch miss is REJECTED.
//!
//! Covered families (all reachable through the Gate-1 `descriptor_by_name` IR-v2 world):
//!   * Merkle membership at depth {2, 4, 8} via the depth-GENERAL builder
//!     ([`membership_descriptor_of_depth`] — the executor's depth-2 pad retired);
//!   * DFA routing (`dfa-routing-toggle-2state::poseidon2-v1`);
//!   * Temporal GTE predicate (`dregg-temporal-predicate-gte::dsl-v1`).
//!
//! Delegation is deliberately NOT here: the emitted delegate descriptors (`dregg-delegate-v2`
//! et al., `lean_descriptor_air.rs`) live in the v1 `parse_descriptor` world, not the IR-v2
//! `EffectVmDescriptor2` world `descriptor_by_name`/`verify_vm_descriptor2` serve — so a "full
//! `verify_vm_descriptor2` of the delegate descriptor" has no Gate-1 target yet (an honest
//! residual, not faked here).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_by_name::{
    MEMBERSHIP_GENERAL_NAME_PREFIX, PredicateKind, descriptor_by_name, descriptor_names_for_kind,
};
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_general::{
    MembershipStep, membership_root, membership_witness,
};
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};

// ─────────────────────────────────────────────────────────────────────────────
// The wire blob = the NEW format. `postcard(Ir2BatchProof)` replaces
// `stark::proof_to_bytes(StarkProof)`. NO air-name rides the blob.
// ─────────────────────────────────────────────────────────────────────────────

fn encode_blob(proof: &Ir2BatchProof<DreggStarkConfig>) -> Vec<u8> {
    postcard::to_allocvec(proof).expect("postcard-encode the BatchProof into the blob table")
}

fn decode_blob(bytes: &[u8]) -> Result<Ir2BatchProof<DreggStarkConfig>, String> {
    postcard::from_bytes(bytes).map_err(|e| format!("blob decode failed: {e}"))
}

/// THE CONSUMER CONTRACT: predicate identity (`pred_name`) → [`descriptor_by_name`] (fail-closed
/// `None`) → decode the blob → [`verify_vm_descriptor2`] against the context public inputs.
///
/// This is exactly what a migrated consumer does: it NEVER reads an air-name out of the blob, it
/// resolves the descriptor from the predicate's committed identity. A dispatch miss is a fail-closed
/// `Err` (never a silent accept). A decode panic is caught and treated as a rejection.
fn consume(pred_name: &str, blob: &[u8], pi: &[BabyBear]) -> Result<(), String> {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let desc = descriptor_by_name(pred_name)
            .ok_or_else(|| format!("fail-closed: no descriptor dispatches for {pred_name:?}"))?;
        let proof = decode_blob(blob)?;
        verify_vm_descriptor2(&desc, &proof, pi)
    }));
    match r {
        Ok(res) => res,
        Err(_) => Err("consumer panicked (treated as rejection)".to_string()),
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// MEMBERSHIP — depth {2, 4, 8} via the depth-GENERAL builder (the depth-2 pad retired).
// ═════════════════════════════════════════════════════════════════════════════

/// A deterministic depth-`d` membership fixture: a fixed leaf + a `d`-step authentication path
/// (alternating direction, distinct siblings). Returns `(leaf, path, root)` where `root =
/// membership_root(leaf, path)` under the descriptor's binary arity-2 chip hash.
fn membership_fixture(depth: usize) -> (BabyBear, Vec<MembershipStep>, BabyBear) {
    let leaf = BabyBear::new(0xABCD);
    let path: Vec<MembershipStep> = (0..depth)
        .map(|i| MembershipStep {
            sibling: BabyBear::new(1000 + i as u32),
            dir: i % 2 == 1,
        })
        .collect();
    let root = membership_root(leaf, &path);
    (leaf, path, root)
}

#[test]
fn membership_roundtrip_depths_2_4_8() {
    for depth in [2usize, 4, 8] {
        // Predicate identity → descriptor NAME → descriptor (the consumer dispatch key).
        let name = format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}{depth}");
        let desc = descriptor_by_name(&name)
            .unwrap_or_else(|| panic!("depth-{depth} membership must dispatch"));
        assert_eq!(
            desc.name, name,
            "dispatched descriptor carries the dispatch key"
        );

        // PRODUCER: honest witness → real proof.
        let (leaf, path, root) = membership_fixture(depth);
        let (trace, pis) = membership_witness(leaf, &path).expect("honest depth witness");
        assert_eq!(pis, vec![leaf, root], "membership PIs are [leaf, root]");
        assert_eq!(trace.len(), depth, "one trace row per Merkle level");
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest depth-{depth} membership must prove: {e}"));

        // WIRE: encode into the blob table (the NEW postcard format).
        let blob = encode_blob(&proof);

        // POSITIVE POLE — honest accept through the full consumer contract.
        consume(&name, &blob, &pis)
            .unwrap_or_else(|e| panic!("honest depth-{depth} membership must ACCEPT: {e}"));

        // NEGATIVE 1 — a forged claimed root (the leaf is not a member under this root).
        let forged_root_pis = vec![leaf, root + BabyBear::ONE];
        assert!(
            consume(&name, &blob, &forged_root_pis).is_err(),
            "depth-{depth}: a forged root PI must be REJECTED"
        );

        // NEGATIVE 2 — a tampered blob (bit-flip in the postcard bytes).
        let mut tampered = blob.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xFF;
        assert!(
            consume(&name, &tampered, &pis).is_err(),
            "depth-{depth}: a tampered blob must be REJECTED"
        );

        // NEGATIVE 3 — cross-KIND descriptor: this membership proof against the DFA descriptor.
        // A wrong dispatch arm cannot launder a proof (structural mismatch → Err).
        assert!(
            consume("dfa-routing-toggle-2state::poseidon2-v1", &blob, &pis).is_err(),
            "depth-{depth}: verifying under the wrong-KIND descriptor must be REJECTED"
        );
    }
}

/// The depth families carry DISTINCT names (⇒ distinct VKs): a depth-4 and a depth-8 membership
/// proof are not interchangeable at the KEY level even though the constraint block is depth-uniform.
/// (This is the VK-separation the name form encodes; it is NOT a verify-time structural reject,
/// which is why `membership_roundtrip_depths_2_4_8` uses cross-KIND — not cross-depth — for its
/// structural negative.)
#[test]
fn membership_depths_have_distinct_dispatch_keys() {
    let d4 = descriptor_by_name(&format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}4")).expect("d4");
    let d8 = descriptor_by_name(&format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}8")).expect("d8");
    assert_ne!(
        d4.name, d8.name,
        "distinct depths ⇒ distinct descriptor names ⇒ distinct VKs"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// DFA routing — the toggle automaton `step(s, y) = s XOR y` over {0,1}.
// (Honest witness mirrors `circuit-prove/tests/dfa_routing_emit_gate.rs`.)
// ═════════════════════════════════════════════════════════════════════════════

const DFA_NAME: &str = "dfa-routing-toggle-2state::poseidon2-v1";
const DFA_WIDTH: usize = 22;
// DFA column layout.
const D_CURRENT: usize = 0;
const D_SYMBOL: usize = 1;
const D_NEXT: usize = 2;
const D_ENTRY_HASH: usize = 3;
const D_RUNNING_HASH: usize = 4;
const D_IS_FIRST: usize = 5;
const D_ZERO_LANE: usize = 6;
const D_ACC: usize = 7;
// DFA PI layout: [initial, final, table_seed, route_commitment].
const D_PI_FINAL: usize = 1;

fn dfa_honest_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let start = 0u32;
    let symbols = [1u32, 0, 0, 0]; // toggle once, then self-loop
    let seed = BabyBear::new(0x51D5);
    let mut cur = start;
    let mut running = seed;
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(4);
    for (i, &sym) in symbols.iter().enumerate() {
        let nxt = cur ^ sym;
        let entry = hash_4_to_1(&[
            BabyBear::new(cur),
            BabyBear::new(sym),
            BabyBear::new(nxt),
            BabyBear::ZERO,
        ]);
        let acc = running;
        running = hash_2_to_1(acc, entry);
        let mut row = vec![BabyBear::ZERO; DFA_WIDTH];
        row[D_CURRENT] = BabyBear::new(cur);
        row[D_SYMBOL] = BabyBear::new(sym);
        row[D_NEXT] = BabyBear::new(nxt);
        row[D_ENTRY_HASH] = entry;
        row[D_RUNNING_HASH] = running;
        row[D_IS_FIRST] = if i == 0 {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
        row[D_ZERO_LANE] = BabyBear::ZERO;
        row[D_ACC] = acc;
        rows.push(row);
        cur = nxt;
    }
    let route = rows[3][D_RUNNING_HASH];
    let pis = vec![BabyBear::new(start), BabyBear::new(cur), seed, route];
    (rows, pis)
}

#[test]
fn dfa_routing_roundtrip() {
    let desc = descriptor_by_name(DFA_NAME).expect("DFA must dispatch");
    let (trace, pis) = dfa_honest_witness();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest DFA route must prove");
    let blob = encode_blob(&proof);

    // Positive.
    consume(DFA_NAME, &blob, &pis).expect("honest DFA route must ACCEPT");
    assert_eq!(pis[D_PI_FINAL], BabyBear::new(1), "toggled 0 → 1 (genuine)");

    // Negative — forged final-state PI (claim a classification you did not reach).
    let mut forged = pis.clone();
    forged[D_PI_FINAL] = BabyBear::new(0);
    assert!(
        consume(DFA_NAME, &blob, &forged).is_err(),
        "a forged DFA final state must be REJECTED"
    );

    // Negative — tampered blob.
    let mut tampered = blob.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xFF;
    assert!(
        consume(DFA_NAME, &tampered, &pis).is_err(),
        "a tampered DFA blob must be REJECTED"
    );

    // Negative — cross-KIND (verify against the temporal descriptor).
    assert!(
        consume("dregg-temporal-predicate-gte::dsl-v1", &blob, &pis).is_err(),
        "DFA proof under the temporal descriptor must be REJECTED"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// Temporal GTE predicate — all values ≥ threshold.
// (Honest witness mirrors `circuit-prove/tests/temporal_predicate_emit_gate.rs`.)
// ═════════════════════════════════════════════════════════════════════════════

const TEMPORAL_NAME: &str = "dregg-temporal-predicate-gte::dsl-v1";
const T_WIDTH: usize = 38;
const T_VALUE: usize = 0;
const T_THRESHOLD: usize = 1;
const T_DIFF: usize = 2;
const T_DIFF_BITS_START: usize = 3;
const T_NUM_DIFF_BITS: usize = 30;
const T_ACCUMULATOR: usize = 33;
const T_STEP_INDEX: usize = 34;
const T_ACC_PLUS_ONE: usize = 35;
const T_STEP_PLUS_ONE: usize = 36;
const T_STATE_ROOT: usize = 37;
// PI layout: [padded_len, threshold, initial_state_root, final_state_root].
const T_PI_THRESHOLD: usize = 1;

fn temporal_row(value: u32, threshold: u32, step: usize, state_root: BabyBear) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; T_WIDTH];
    row[T_VALUE] = BabyBear::new(value);
    row[T_THRESHOLD] = BabyBear::new(threshold);
    let diff = BabyBear::new(value) - BabyBear::new(threshold);
    row[T_DIFF] = diff;
    let diff_u = diff.as_u32();
    for i in 0..T_NUM_DIFF_BITS {
        row[T_DIFF_BITS_START + i] = BabyBear::new((diff_u >> i) & 1);
    }
    let acc = (step + 1) as u32;
    row[T_ACCUMULATOR] = BabyBear::new(acc);
    row[T_STEP_INDEX] = BabyBear::new(step as u32);
    row[T_ACC_PLUS_ONE] = BabyBear::new(acc + 1);
    row[T_STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);
    row[T_STATE_ROOT] = state_root;
    row
}

fn temporal_honest_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let threshold = 50u32;
    let values = [100u32, 100, 100];
    let roots = [
        BabyBear::new(1000),
        BabyBear::new(1001),
        BabyBear::new(1002),
    ];
    let num_steps = 3usize;
    let padded = 4usize;
    let final_root = roots[num_steps - 1];
    let mut trace = Vec::with_capacity(padded);
    for step in 0..padded {
        let value = if step < num_steps {
            values[step]
        } else {
            values[num_steps - 1]
        };
        let sr = if step < num_steps {
            roots[step]
        } else {
            final_root
        };
        trace.push(temporal_row(value, threshold, step, sr));
    }
    let pis = vec![
        BabyBear::new(padded as u32),
        BabyBear::new(threshold),
        roots[0],
        final_root,
    ];
    (trace, pis)
}

#[test]
fn temporal_predicate_roundtrip() {
    let desc = descriptor_by_name(TEMPORAL_NAME).expect("temporal must dispatch");
    let (trace, pis) = temporal_honest_witness();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest temporal GTE run must prove");
    let blob = encode_blob(&proof);

    // Positive.
    consume(TEMPORAL_NAME, &blob, &pis).expect("honest temporal run must ACCEPT");

    // Negative — forged threshold PI (row-0 THRESHOLD PiBinding).
    let mut forged = pis.clone();
    forged[T_PI_THRESHOLD] = pis[T_PI_THRESHOLD] + BabyBear::ONE;
    assert!(
        consume(TEMPORAL_NAME, &blob, &forged).is_err(),
        "a forged temporal threshold PI must be REJECTED"
    );

    // Negative — tampered blob.
    let mut tampered = blob.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xFF;
    assert!(
        consume(TEMPORAL_NAME, &tampered, &pis).is_err(),
        "a tampered temporal blob must be REJECTED"
    );

    // Negative — cross-KIND (verify against the DFA descriptor).
    assert!(
        consume(DFA_NAME, &blob, &pis).is_err(),
        "temporal proof under the DFA descriptor must be REJECTED"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// DISPATCH fail-closed — the #1 migration danger. A miss is a fail-closed reject,
// never a silent accept; the off-STARK Pedersen family has NO descriptor.
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn dispatch_is_fail_closed_on_miss() {
    // An honest, well-formed blob (a real membership proof) is still REJECTED under an unknown
    // predicate name — the consumer never falls through to accept.
    let (leaf, path, _root) = membership_fixture(2);
    let (trace, pis) = membership_witness(leaf, &path).expect("witness");
    let name = format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}2");
    let desc = descriptor_by_name(&name).expect("dispatch");
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("prove");
    let blob = encode_blob(&proof);

    for miss in [
        "no-such-air",
        "",
        "merkle-membership",
        "pedersen-equality",
        "schnorr-equality",
    ] {
        assert!(
            descriptor_by_name(miss).is_none(),
            "{miss:?} must not resolve to any descriptor"
        );
        assert!(
            consume(miss, &blob, &pis).is_err(),
            "{miss:?}: a dispatch miss must fail closed (reject), never silently accept"
        );
    }

    // The off-STARK Pedersen-equality family has NO descriptor at all (empty name list).
    assert!(descriptor_names_for_kind(PredicateKind::PedersenEquality).is_empty());
}
