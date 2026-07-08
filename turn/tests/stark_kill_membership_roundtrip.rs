//! # RUNTIME round-trip gate for the turn-membership STARK-kill wire migration.
//!
//! The migration flips the opaque proof blob at the `MerkleMembership` /
//! neighbor-adjacency predicate seam from `stark::proof_to_bytes(StarkProof)` to
//! `postcard(Ir2BatchProof)`, and the consumers from `verify_membership_dsl` /
//! `verify_adjacency` to `descriptor_by_name(..) -> verify_vm_descriptor2`. Both
//! the byte format and the descriptor dispatch are INVISIBLE to `cargo build`
//! (the blob is an opaque `Vec<u8>`), so a build-green edit can still be wrong at
//! RUNTIME. This is the gate the build cannot give: it drives the REAL producer →
//! wire → consumer path end-to-end, per predicate, with an honest ACCEPT and
//! several non-vacuous REJECTs (forged / tampered / cross-shape).
//!
//! It uses ONLY the public `membership_verifier` surface the ~8 app crates use
//! (`prove_sender_membership` / `MerkleMembershipStarkVerifier`,
//! `prove_neighbor_adjacency` / `CircuitNeighborAdjacencyVerifier`), so a green
//! run here is the same path they exercise through `registry_with_real_verifiers`.

use dregg_cell::predicate::{
    NeighborAdjacencyVerifier, PredicateInput, WitnessedPredicateVerifier,
};
use dregg_circuit::BabyBear;
use dregg_circuit::dsl::membership::create_test_witness;
use dregg_circuit::poseidon2::hash_2_to_1;
use dregg_turn::executor::membership_verifier::{
    CircuitNeighborAdjacencyVerifier, MerkleMembershipStarkVerifier, NeighborAdjStep,
    adjacency_commitment_bytes, adjacency_leaf_felt, authorized_set_root_bytes,
    prove_neighbor_adjacency, prove_sender_membership,
};

/// THE canonical chip-native membership compress (the executor's leaf domain).
fn compress(bytes: &[u8; 32]) -> BabyBear {
    dregg_commit::typed::compress_member(bytes)
}

// ══════════════════════════════════════════════════════════════════════════════
// MERKLE MEMBERSHIP — prove_sender_membership → MembershipProofWire →
// MerkleMembershipStarkVerifier (postcard(Ir2BatchProof) + 4-ary descriptor).
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn membership_wire_roundtrip_honest_accept_and_rejects() {
    // A genuine depth-4 4-ary Merkle path (a power-of-two depth).
    let member = [0x11u8; 32];
    let leaf = compress(&member);
    let (sibs, pos, _root) = create_test_witness(leaf, 4);

    // PRODUCER: real prove → the NEW wire blob (depth || postcard(Ir2BatchProof)).
    let proof = prove_sender_membership(&member, &sibs, &pos).expect("prove membership");
    let root_bytes = authorized_set_root_bytes(&member, &sibs, &pos);

    let v = MerkleMembershipStarkVerifier;

    // POSITIVE POLE — honest member ACCEPTS through the real verify_vm_descriptor2
    // consumer (decode blob → descriptor_by_name(depth) → verify [leaf, root]).
    v.verify(&root_bytes, &PredicateInput::Sender(&member), &proof)
        .expect("honest depth-4 member must ACCEPT through the descriptor consumer");

    // NEGATIVE 1 — a non-member sender against the SAME committed root, reusing the
    // member's proof: the committed leaf is compress(intruder) != the proof's leaf
    // pin, so the descriptor's row-0 leaf PiBinding fails.
    let intruder = [0x99u8; 32];
    assert!(
        v.verify(&root_bytes, &PredicateInput::Sender(&intruder), &proof)
            .is_err(),
        "a non-member sender (stolen proof) must be REJECTED (leaf pin mismatch)"
    );

    // NEGATIVE 2 — the intruder's OWN honest proof, but against the member's root:
    // their path authenticates to a DIFFERENT root, so the last-row root PiBinding
    // fails. (A non-member cannot forge a path to the committed root.)
    let forged = prove_sender_membership(&intruder, &sibs, &pos).expect("prove intruder");
    assert!(
        v.verify(&root_bytes, &PredicateInput::Sender(&intruder), &forged)
            .is_err(),
        "a self-fabricated proof against another's root must be REJECTED (root pin mismatch)"
    );

    // NEGATIVE 3 — a tampered blob (bit-flip inside the postcard(Ir2BatchProof)
    // region): decode/verify must FAIL CLOSED (Err), never panic.
    let mut tampered = proof.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xFF;
    assert!(
        v.verify(&root_bytes, &PredicateInput::Sender(&member), &tampered)
            .is_err(),
        "a tampered membership blob must be REJECTED (fail-closed), not panic"
    );

    // NEGATIVE 4 — an empty blob (a decode miss is a fail-closed reject).
    assert!(
        v.verify(&root_bytes, &PredicateInput::Sender(&member), &[])
            .is_err(),
        "an empty membership blob must be REJECTED"
    );
}

#[test]
fn membership_wire_roundtrip_depth3_padded_root_is_production_faithful() {
    // depth 3 is NOT a power of two. The producer pads the path to depth 4 with
    // zero-sibling position-0 levels — EXACTLY how generate_merkle_poseidon2_trace
    // pads — so the descriptor's committed root is BYTE-EQUAL to the production
    // authorized_set_root_bytes. An honest ACCEPT is the faithful-padding witness;
    // a change to either padding rule would flip this to a root-pin rejection.
    let member = [0x22u8; 32];
    let leaf = compress(&member);
    let (sibs, pos, _root) = create_test_witness(leaf, 3);

    let proof = prove_sender_membership(&member, &sibs, &pos).expect("prove padded membership");
    let root_bytes = authorized_set_root_bytes(&member, &sibs, &pos);

    let v = MerkleMembershipStarkVerifier;
    v.verify(&root_bytes, &PredicateInput::Sender(&member), &proof)
        .expect("depth-3-padded membership must ACCEPT (descriptor root == production root)");

    // Non-vacuity: a non-member is still rejected at the padded root.
    let intruder = [0x77u8; 32];
    assert!(
        v.verify(&root_bytes, &PredicateInput::Sender(&intruder), &proof)
            .is_err(),
        "a non-member must be REJECTED at the padded root too"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// NEIGHBOR ADJACENCY — prove_neighbor_adjacency → AdjacencyProofWire →
// CircuitNeighborAdjacencyVerifier (postcard(Ir2BatchProof) + adjacency descriptor).
// ══════════════════════════════════════════════════════════════════════════════

/// Build the binary Poseidon2 tree levels over `compress(neighbor)` leaves.
fn tree_levels(neighbors: &[[u8; 32]]) -> Vec<Vec<BabyBear>> {
    let leaves: Vec<BabyBear> = neighbors.iter().map(adjacency_leaf_felt).collect();
    let mut levels = vec![leaves];
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        let next: Vec<BabyBear> = cur.chunks(2).map(|p| hash_2_to_1(p[0], p[1])).collect();
        levels.push(next);
    }
    levels
}

fn auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<NeighborAdjStep> {
    let depth = levels.len() - 1;
    let mut path = Vec::with_capacity(depth);
    for level in &levels[..depth] {
        let is_right = index & 1 == 1;
        let sibling = if is_right {
            level[index - 1]
        } else {
            level[index + 1]
        };
        path.push(NeighborAdjStep {
            sibling,
            dir: is_right,
        });
        index >>= 1;
    }
    path
}

#[test]
fn adjacency_wire_roundtrip_honest_accept_and_rejects() {
    // Four sorted leaves; the two MIDDLE ones (indices 1,2) are consecutive.
    let neighbors: [[u8; 32]; 4] = [[0x10u8; 32], [0x20u8; 32], [0x30u8; 32], [0x40u8; 32]];
    let levels = tree_levels(&neighbors);
    let root_felt = levels.last().unwrap()[0];
    let commitment = adjacency_commitment_bytes(root_felt);

    let lower = neighbors[1];
    let upper = neighbors[2];
    let lp = auth_path(&levels, 1);
    let up = auth_path(&levels, 2);

    // PRODUCER: real prove → the NEW wire (idx_lower || idx_upper || postcard(proof)).
    let adjacency_proof = prove_neighbor_adjacency(&lower, &lp, &upper, &up)
        .expect("consecutive neighbors must produce an adjacency proof");

    let v = CircuitNeighborAdjacencyVerifier;

    // POSITIVE POLE — honest consecutive pair ACCEPTS through verify_vm_descriptor2.
    v.verify_adjacency(&commitment, &lower, &upper, &adjacency_proof)
        .expect("honest consecutive adjacency must ACCEPT through the descriptor consumer");

    // NEGATIVE 1 — a wrong committed root: the last-row root pin fails.
    let wrong_commitment = adjacency_commitment_bytes(root_felt + BabyBear::ONE);
    assert!(
        v.verify_adjacency(&wrong_commitment, &lower, &upper, &adjacency_proof)
            .is_err(),
        "a wrong committed root must be REJECTED (root pin)"
    );

    // NEGATIVE 2 — a tampered blob: decode/verify must FAIL CLOSED, never panic.
    let mut tampered = adjacency_proof.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xFF;
    assert!(
        v.verify_adjacency(&commitment, &lower, &upper, &tampered)
            .is_err(),
        "a tampered adjacency blob must be REJECTED (fail-closed), not panic"
    );

    // NEGATIVE 3 — the WIDE BRACKET forge: leaves 0 and 3 are NOT consecutive. The
    // honest prover refuses to build it (the census-R1 double-spend defense).
    let wide_lp = auth_path(&levels, 0);
    let wide_up = auth_path(&levels, 3);
    let wide_err =
        prove_neighbor_adjacency(&neighbors[0], &wide_lp, &neighbors[3], &wide_up).unwrap_err();
    assert!(
        wide_err.contains("not consecutive"),
        "a non-consecutive wide bracket must be REFUSED at prove time; got {wide_err}"
    );

    // NEGATIVE 4 — a GENUINE consecutive proof cannot be REPLAYED under different
    // neighbor leaves: it attests (0x20, 0x30); presenting it for (0x10, 0x40)
    // fails the leaf PiBindings (the STARK binds the specific leaves it attests).
    assert!(
        v.verify_adjacency(&commitment, &neighbors[0], &neighbors[3], &adjacency_proof)
            .is_err(),
        "a consecutive proof must not verify under different neighbor leaves"
    );

    // NEGATIVE 5 — an empty adjacency blob is a fail-closed reject.
    assert!(
        v.verify_adjacency(&commitment, &lower, &upper, &[])
            .is_err(),
        "an empty adjacency blob must be REJECTED"
    );
}
