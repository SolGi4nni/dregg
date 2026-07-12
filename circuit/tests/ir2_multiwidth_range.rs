//! MULTI-WIDTH RANGE TABLES — the IR-2 realization of the availability-weld 15-bit teeth.
//!
//! The hardened `…-v1-avail` transfer/burn members (Lean `transferVmDescriptorAvail` /
//! `burnVmDescriptorAvail`, lifted `v3OfFrozenWide`) lower their 15-bit borrow-limb range checks
//! into a WIDTH-TAGGED custom range table (Lean `rangeTidW 15 = .custom 79` → wire id 84) beside
//! the shared 30-bit `.range` table. This exercises the Rust interpreter's multi-range-table
//! routing (`MainLayout::build`): both widths realize the byte-limb decomposition at their OWN
//! width, in-range witnesses prove, and a 15-bit overflow — the exact wrap window the
//! availability forgery needs — is REFUSED.

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

/// The Lean `rangeTidW 15` wire id: `.custom (64 + 15)` → `5 + 79 = 84`.
const W15_WIRE_ID: usize = 84;

fn w15_descriptor_json() -> String {
    format!(
        concat!(
            "{{\"name\":\"ir2-range-w15-test\",\"ir\":2,\"trace_width\":2,",
            "\"public_input_count\":0,\"tables\":[",
            "{{\"id\":0,\"name\":\"main\",\"arity\":2,\"sem\":\"main\"}},",
            "{{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30}},",
            "{{\"id\":{w15},\"name\":\"range_w15\",\"arity\":1,\"sem\":\"range\",\"bits\":15}}],",
            "\"constraints\":[",
            "{{\"t\":\"lookup\",\"table\":2,\"tuple\":[{{\"t\":\"var\",\"v\":0}}]}},",
            "{{\"t\":\"lookup\",\"table\":{w15},\"tuple\":[{{\"t\":\"var\",\"v\":1}}]}}],",
            "\"hash_sites\":[],\"ranges\":[]}}"
        ),
        w15 = W15_WIRE_ID
    )
}

fn trace(col0: u32, col1: u32) -> Vec<Vec<BabyBear>> {
    (0..8)
        .map(|_| vec![BabyBear::new(col0), BabyBear::new(col1)])
        .collect()
}

/// In-range at BOTH widths (30-bit max + 15-bit max) proves and verifies.
#[test]
fn multi_width_range_tables_prove_and_verify() {
    let desc = parse_vm_descriptor2(&w15_descriptor_json())
        .expect("the multi-width range descriptor parses");
    let t = trace((1 << 30) - 1, (1 << 15) - 1);
    let proof = prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[])
        .expect("an in-range multi-width witness proves");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("the multi-width proof verifies");
}

/// A 15-bit overflow in the width-tagged wire is REFUSED — the wire value `2^15` has no
/// decomposition witness (this is the wrap window the availability forgery rides; the 30-bit
/// table alone would have admitted it).
#[test]
fn w15_overflow_is_refused() {
    let desc = parse_vm_descriptor2(&w15_descriptor_json())
        .expect("the multi-width range descriptor parses");
    let t = trace(5, 1 << 15);
    assert!(
        prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
        "a 15-bit overflow must have no satisfying assembly under the 15-bit table"
    );
}

/// The same value IS admitted by the 30-bit wire — the widths are genuinely per-table (the
/// refusal above is the 15-bit tooth, not a global clamp).
#[test]
fn w30_wire_admits_what_w15_refuses() {
    let desc = parse_vm_descriptor2(&w15_descriptor_json())
        .expect("the multi-width range descriptor parses");
    let t = trace(1 << 15, 7);
    let proof = prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[])
        .expect("2^15 fits the 30-bit wire");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("verifies");
}
