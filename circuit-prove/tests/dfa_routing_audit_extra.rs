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

/// ⚑ **THE EMITTED ARTIFACT ITSELF, NOT A COPY OF IT (2026-08-06).** This was an inline
/// `r#"…"#` transcription of the Lean `#guard` bytes, and the `challenges` flag day
/// (2026-08-05) broke it along with 27 siblings: the artifact under
/// `circuit/descriptors/` was re-emitted, the literal was not, and
/// `parse_vm_descriptor2` refused it with `ir:2 descriptor missing "challenges"`. An
/// inline golden is a copy that no re-emit reaches, so every flag day breaks exactly
/// that set again — the fix is to have no copy. `check-emit-gate-weld.py` still gates
/// the literals that remain (the descriptors with no checked-in artifact to name), and
/// `check-descriptor-drift.sh` gates this file against its Lean author.
const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/dfa-routing.json");

const CURRENT: usize = 0;
const SYMBOL: usize = 1;
const NEXT: usize = 2;
const ENTRY_HASH: usize = 3;
const RUNNING_HASH: usize = 4;
const IS_FIRST: usize = 5;
const ZERO_LANE: usize = 6;
const ACC: usize = 7;
/// E7 narrowed both chip lookups onto the NARROW bus, deleting the 2 x 7 lane columns.
const DFA_WIDTH: usize = 8;
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
        row[IS_FIRST] = if i == 0 {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
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
