//! ADVERSARIAL AUDIT — one additional isolating tamper the dfa_routing_emit_gate did NOT do:
//! forge the `initial_state` public input (PI_INITIAL). The honest proof re-verified against a
//! forged initial-state PI must be refused by the B1 first-row `PiBinding` (col CURRENT ← pi[0]).
//! This is disjoint from the five existing canaries (final/route/seed/forbidden-edge/running-hash).

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};

const GOLDEN_JSON: &str = r#"{"name":"dfa-routing-toggle-2state::poseidon2-v1","ir":2,"trace_width":22,"public_input_count":4,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":4},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":6},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":3},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":7},{"t":"var","v":3},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":4},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21}]},{"t":"gate","body":{"t":"var","v":6}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":1},"r":{"t":"add","l":{"t":"var","v":1},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"var","v":1}}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"first","col":7,"pi_index":2},{"t":"pi_binding","row":"last","col":2,"pi_index":1},{"t":"pi_binding","row":"last","col":4,"pi_index":3}],"hash_sites":[],"ranges":[]}"#;

const CURRENT: usize = 0;
const SYMBOL: usize = 1;
const NEXT: usize = 2;
const ENTRY_HASH: usize = 3;
const RUNNING_HASH: usize = 4;
const IS_FIRST: usize = 5;
const ZERO_LANE: usize = 6;
const ACC: usize = 7;
const DFA_WIDTH: usize = 22;
const PI_INITIAL: usize = 0;

fn step(s: u32, y: u32) -> u32 {
    s ^ y
}

fn honest_witness(start: u32, sym0: u32, seed: BabyBear) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let symbols = [sym0, 0, 0, 0];
    let mut cur = start;
    let mut running = seed;
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(4);
    for (i, &sym) in symbols.iter().enumerate() {
        let nxt = step(cur, sym);
        let entry = hash_4_to_1(&[
            BabyBear::new(cur),
            BabyBear::new(sym),
            BabyBear::new(nxt),
            BabyBear::ZERO,
        ]);
        let acc = running;
        running = hash_2_to_1(acc, entry);
        let mut row = vec![BabyBear::ZERO; DFA_WIDTH];
        row[CURRENT] = BabyBear::new(cur);
        row[SYMBOL] = BabyBear::new(sym);
        row[NEXT] = BabyBear::new(nxt);
        row[ENTRY_HASH] = entry;
        row[RUNNING_HASH] = running;
        row[IS_FIRST] = if i == 0 { BabyBear::ONE } else { BabyBear::ZERO };
        row[ACC] = acc;
        rows.push(row);
        cur = nxt;
    }
    let route = rows[3][RUNNING_HASH];
    let pis = vec![BabyBear::new(start), BabyBear::new(cur), seed, route];
    (rows, pis)
}

/// Forge the `initial_state` PI: the honest proof must fail the B1 first-row PiBinding.
#[test]
fn forged_initial_state_refuses() {
    let desc: EffectVmDescriptor2 = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_witness(0, 1, BabyBear::new(0x51D5));
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest proves");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("honest verifies — else vacuous");
    let mut forged = pis.clone();
    forged[PI_INITIAL] = pis[PI_INITIAL] + BabyBear::ONE; // claim we started in state 1, not 0
    assert_ne!(forged[PI_INITIAL], pis[PI_INITIAL]);
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged initial_state must fail the B1 first-row PiBinding"
    );
}
