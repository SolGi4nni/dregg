//! ADVERSARIAL AUDIT — one additional isolating tamper the implementer did not write.
//!
//! Targets relational C7 (the gated range RECOMPOSITION `Σ 2^i·bit_i == diff`), a constraint
//! that NONE of the shipped canaries bite (they hit C1 pin, C8 high-bit, C14 chip lookup).
//! We corrupt ONE diff bit so the bit-decomposition no longer recomposes to `diff`, while
//! keeping every bit binary (C6 holds) and the high bit clear (C8 holds). Only C7 can bite.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_2_to_1;

const RELATIONAL_GOLDEN: &str = r#"{"name":"dregg-relational-predicate-ir2-v1","ir":2,"trace_width":59,"public_input_count":3,"tables":[],"constraints":[{"t":"pi_binding","row":"first","col":36,"pi_index":2},{"t":"gate","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"const","v":-1}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"var","v":2}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":37}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":38}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":39}}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":14},"r":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":17},"r":{"t":"add","l":{"t":"var","v":17},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"var","v":18},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"var","v":19},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"var","v":21},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"var","v":22},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"var","v":23},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"add","l":{"t":"var","v":27},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":28},"r":{"t":"add","l":{"t":"var","v":28},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":29},"r":{"t":"add","l":{"t":"var","v":29},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":30},"r":{"t":"add","l":{"t":"var","v":30},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":31},"r":{"t":"add","l":{"t":"var","v":31},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":33},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":34},"r":{"t":"add","l":{"t":"var","v":34},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":5}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2},"r":{"t":"var","v":6}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4},"r":{"t":"var","v":7}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32},"r":{"t":"var","v":10}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":64},"r":{"t":"var","v":11}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":128},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":256},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":512},"r":{"t":"var","v":14}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1024},"r":{"t":"var","v":15}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2048},"r":{"t":"var","v":16}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4096},"r":{"t":"var","v":17}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8192},"r":{"t":"var","v":18}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16384},"r":{"t":"var","v":19}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":20}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":21}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":131072},"r":{"t":"var","v":22}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":262144},"r":{"t":"var","v":23}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":524288},"r":{"t":"var","v":24}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1048576},"r":{"t":"var","v":25}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2097152},"r":{"t":"var","v":26}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4194304},"r":{"t":"var","v":27}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8388608},"r":{"t":"var","v":28}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16777216},"r":{"t":"var","v":29}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":33554432},"r":{"t":"var","v":30}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":67108864},"r":{"t":"var","v":31}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":134217728},"r":{"t":"var","v":32}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":268435456},"r":{"t":"var","v":33}},"r":{"t":"mul","l":{"t":"const","v":536870912},"r":{"t":"var","v":34}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"var","v":34}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"var","v":4}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":35}},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":43},"r":{"t":"add","l":{"t":"var","v":43},"r":{"t":"const","v":-1}}}},{"t":"pi_binding","row":"first","col":41,"pi_index":0},{"t":"pi_binding","row":"first","col":42,"pi_index":1},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":0},{"t":"var","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":41},{"t":"var","v":45},{"t":"var","v":46},{"t":"var","v":47},{"t":"var","v":48},{"t":"var","v":49},{"t":"var","v":50},{"t":"var","v":51}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":2},{"t":"var","v":3},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":42},{"t":"var","v":52},{"t":"var","v":53},{"t":"var","v":54},{"t":"var","v":55},{"t":"var","v":56},{"t":"var","v":57},{"t":"var","v":58}]},{"t":"gate","body":{"t":"var","v":44}}],"hash_sites":[],"ranges":[]}"#;

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Err(_) | Ok(Err(_)))
}

fn relational_row() -> Vec<BabyBear> {
    let (va, ba, vb, bb) = (100u32, 7u32, 40u32, 9u32);
    let diff = va - vb; // 60
    let mut r = vec![BabyBear::ZERO; 59];
    r[0] = BabyBear::new(va);
    r[1] = BabyBear::new(ba);
    r[2] = BabyBear::new(vb);
    r[3] = BabyBear::new(bb);
    r[4] = BabyBear::new(diff);
    for i in 0..30 {
        r[5 + i] = BabyBear::new((diff >> i) & 1);
    }
    r[36] = BabyBear::ONE;
    r[37] = BabyBear::ONE; // range_flag
    r[41] = hash_2_to_1(BabyBear::new(va), BabyBear::new(ba));
    r[42] = hash_2_to_1(BabyBear::new(vb), BabyBear::new(bb));
    r[43] = BabyBear::ONE;
    r
}

/// Honest baseline: proves and verifies (non-vacuity floor for THIS tamper).
#[test]
fn extra_relational_honest_accepts() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let r = relational_row();
    let trace = vec![r.clone(), r.clone(), r.clone(), r.clone()];
    let pis = vec![r[41], r[42], BabyBear::ONE];
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest relational must accept"
    );
}

/// C7 ISOLATION: flip diff_bit_0 (col 5) from 0 to 1. diff=60 has bit0=0, so the recomposition
/// Σ 2^i·bit_i becomes 61 ≠ 60 = diff → C7 bites. The bit stays binary (C6 holds), the high bit
/// stays clear (C8 holds), diff itself unchanged (C9/C10 gated off). ONLY C7 can reject.
#[test]
fn extra_relational_broken_recomposition_refuses() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let base = relational_row();
    // sanity: bit 0 of diff (60) is 0, so setting it to 1 is a genuine recomposition break.
    assert_eq!(base[5], BabyBear::ZERO, "diff_bit_0 of 60 must be 0");
    let mut bad = base.clone();
    bad[5] = BabyBear::ONE; // recompose -> 61, diff still 60
    let trace = vec![bad.clone(), bad.clone(), bad.clone(), bad.clone()];
    let pis = vec![base[41], base[42], BabyBear::ONE];
    assert!(
        rejects(&desc, &trace, &pis),
        "a bit-decomposition that does not recompose to diff must be REJECTED (C7)"
    );
}
