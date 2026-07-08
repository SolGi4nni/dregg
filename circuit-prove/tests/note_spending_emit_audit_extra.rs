//! ADVERSARIAL non-vacuity extra tamper (audit-only, additive).
//!
//! The shipped gate probes forged nullifier/root/mint PIs (PiBinding teeth) and a tampered Merkle
//! sibling (the C6 membership lookup). None of them isolates the FULL-WIDTH 28-limb commitment
//! `hash_fact` chain (C2a..C2g). This test tampers a commitment PREIMAGE limb (col 20, OWNER_START)
//! WITHOUT recomputing the chain output col 48 — so the C2a `Poseidon2Chip` lookup names an out0 no
//! genuine permutation of the tampered inputs serves → LookupError. It first re-asserts the honest
//! witness ACCEPTS (non-vacuity), then asserts the tampered trace is REJECTED.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::note_spending::generate_note_spending_trace;
use dregg_circuit::field::BabyBear;
use dregg_circuit::note_spending_air::{
    NOTE_SPENDING_WIDTH, NoteSpendingWitness, pi, limb_col, test_spending_key,
};
use dregg_circuit::poseidon2::{hash_fact, hash_many};
use dregg_circuit_prove::note_spend_leaf_adapter::{
    note_spend_leaf_public_inputs, note_spend_to_descriptor2,
};

const EXT_BASE_WIDTH: usize = NOTE_SPENDING_WIDTH + 3;

fn make_witness(tag: u8) -> NoteSpendingWitness {
    let owner = [tag; 32];
    let nonce = [tag ^ 0x5A; 32];
    let rand = [tag ^ 0xA5; 32];
    let key = test_spending_key(tag as u32 + 0x77);
    let depth = 2;
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        siblings.push([
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
        ]);
        positions.push((i % 4) as u8);
    }
    NoteSpendingWitness::from_note_limbs(
        &owner, 0xDEAD_BEEF_CAFE, 3, &nonce, &rand, key, siblings, positions,
    )
}

fn honest_base_trace(w: &NoteSpendingWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (mut trace, pis) = generate_note_spending_trace(w);
    for row in &mut trace {
        row.resize(EXT_BASE_WIDTH, BabyBear::ZERO);
    }
    let m1 = hash_fact(
        pis[pi::NULLIFIER],
        &[
            pis[pi::MERKLE_ROOT],
            pis[pi::DESTINATION_FEDERATION],
            pis[pi::ASSET_TYPE],
        ],
    );
    let mint = hash_fact(m1, &[pis[pi::VALUE], pis[pi::VALUE_HI]]);
    trace[0][NOTE_SPENDING_WIDTH] = pis[pi::MERKLE_ROOT];
    trace[0][NOTE_SPENDING_WIDTH + 1] = m1;
    trace[0][NOTE_SPENDING_WIDTH + 2] = mint;
    let full_pis = note_spend_leaf_public_inputs(w);
    (trace, full_pis)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    !matches!(r, Ok(Ok(())))
}

#[test]
fn tampered_commitment_limb_refuses() {
    let desc = note_spend_to_descriptor2().expect("production lowering builds");
    let w = make_witness(0x65);
    let (mut trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "non-vacuity: honest witness must be accepted"
    );
    // Tamper the first commitment preimage limb (owner limb 0, col 20) on the commitment row (row 0)
    // WITHOUT recomputing the C2a chain output col 48. The C2a Poseidon2Chip lookup now names an out0
    // no genuine permutation of the tampered [col20..col24] serves → the commitment-chain tooth bites.
    trace[0][limb_col::OWNER_START] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &pis),
        "a tampered commitment preimage limb must be REJECTED (C2a commitment-chain lookup)"
    );
}
