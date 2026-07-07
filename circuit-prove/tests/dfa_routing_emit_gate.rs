//! # The emit-from-Lean EQUALITY GATE — DFA message routing (`dregg-dfa-routing-v1`).
//!
//! Validates the `emit-from-Lean` pattern end-to-end on the DFA-routing family: the descriptor is
//! AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/DfaRoutingEmit.lean`, `dfaRoutingDesc`) and
//! its wire string is byte-pinned there (`emitVmJson2` `#guard`). This test embeds that EXACT
//! string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. KATs the two chip mappings this family needs: an arity-4 `TID_P2` absorb IS `hash_4_to_1`
//!      (the entry hash) and an arity-2 absorb IS `hash_2_to_1` (the running-hash step);
//!   3. proves an HONEST routing witness (a real toggle-DFA run whose per-step `(state, symbol,
//!      next)` chain is committed by a rolling Poseidon2 route commitment) through
//!      [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies against the public inputs;
//!   4. the MUTATION CANARIES — each tampers the honest statement and asserts a REAL UNSAT, by a
//!      NAMED constraint:
//!        * forged `final_state` (B2 last-row `PiBinding`) — can't claim a classification you didn't reach;
//!        * forged `route_commitment` (B3 last-row `PiBinding`) — the commitment binds the trace;
//!        * forged `table_commitment` seed (first-row `acc` `PiBinding`) — can't reuse a route under a
//!          different table;
//!        * a FORBIDDEN routed edge (`next != step(state, symbol)`, the GAP-A transition `Gate`) —
//!          can't route along an edge the table forbids;
//!        * a forged running hash (the arity-2 chip `Lookup` binding) — a fabricated commitment step
//!          names an unserved chip row.
//!
//! Every canary is NON-VACUOUS by construction: the honest witness proves+verifies (step 3), and
//! each negative is asserted alongside a positive re-check that the honest statement is accepted.
//!
//! The concrete DFA is the minimal TOGGLE automaton over states `{0,1}`, symbols `{0,1}`,
//! `step(s,y) = s XOR y`. Its bivariate interpolant `cur + sym − 2·cur·sym` (emitted as the GAP-A
//! `Gate`) IS the polynomial the production `TableFunction` Lagrange expansion computes; the
//! grid-vanishing gates `cur·(cur−1)`, `sym·(sym−1)` pin the inputs to `{0,1}`.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 dfaRoutingDesc` emits (pinned by the `#guard`
/// in `DfaRoutingEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this literal drifts,
/// the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dfa-routing-toggle-2state::poseidon2-v1","ir":2,"trace_width":22,"public_input_count":4,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":4},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":6},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":3},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":7},{"t":"var","v":3},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":4},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21}]},{"t":"gate","body":{"t":"var","v":6}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":1},"r":{"t":"add","l":{"t":"var","v":1},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"var","v":1}}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"first","col":7,"pi_index":2},{"t":"pi_binding","row":"last","col":2,"pi_index":1},{"t":"pi_binding","row":"last","col":4,"pi_index":3}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `DfaRoutingEmit.lean` §1). ---
const CURRENT: usize = 0;
const SYMBOL: usize = 1;
const NEXT: usize = 2;
const ENTRY_HASH: usize = 3;
const RUNNING_HASH: usize = 4;
const IS_FIRST: usize = 5;
const ZERO_LANE: usize = 6;
const ACC: usize = 7;
const ENTRY_LANE_BASE: usize = 8;
const RUNNING_LANE_BASE: usize = 15;
const DFA_WIDTH: usize = 22;

// --- Public-input layout. ---
const PI_INITIAL: usize = 0;
const PI_FINAL: usize = 1;
const PI_TABLE: usize = 2;
const PI_ROUTE: usize = 3;

/// A `TID_P2` chip lookup absorbing `input_cols` (arity = `input_cols.len()`), binding out0 to
/// `out_col` and lanes 1..7 to `lane_base..lane_base+7`. Built EXACTLY as Lean's `chipLookupTuple`
/// (arity tag = number of inputs, `CHIP_RATE` zero-padded inputs, then out0 :: 7 lanes).
fn chip_lookup(input_cols: &[usize], out_col: usize, lane_base: usize) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(input_cols.len() as i64)); // arity tag (= ins.length in Lean)
    for i in 0..CHIP_RATE {
        tuple.push(match input_cols.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(out_col)); // out0 = the digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The independently-hand-built twin of the Lean `dfaRoutingDesc` (the "hand AIR semantics" shape):
/// the two child hashes, five per-row Base gates, two transition WindowGates, and the five boundary
/// pins — in the exact order the Lean emit lists them.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let g = |body: LeanExpr| VmConstraint2::Base(VmConstraint::Gate(body));

    // is_first · (is_first − 1)
    let is_first_bool = g(LeanExpr::mul(
        LeanExpr::Var(IS_FIRST),
        LeanExpr::add(LeanExpr::Var(IS_FIRST), LeanExpr::Const(-1)),
    ));
    // current · (current − 1)
    let state_grid = g(LeanExpr::mul(
        LeanExpr::Var(CURRENT),
        LeanExpr::add(LeanExpr::Var(CURRENT), LeanExpr::Const(-1)),
    ));
    // symbol · (symbol − 1)
    let symbol_grid = g(LeanExpr::mul(
        LeanExpr::Var(SYMBOL),
        LeanExpr::add(LeanExpr::Var(SYMBOL), LeanExpr::Const(-1)),
    ));
    // next − (current + symbol − 2·current·symbol) — the toggle bivariate interpolant.
    let toggle_interp = LeanExpr::add(
        LeanExpr::add(LeanExpr::Var(CURRENT), LeanExpr::Var(SYMBOL)),
        LeanExpr::mul(
            LeanExpr::Const(-2),
            LeanExpr::mul(LeanExpr::Var(CURRENT), LeanExpr::Var(SYMBOL)),
        ),
    );
    let transition = g(LeanExpr::add(
        LeanExpr::Var(NEXT),
        LeanExpr::mul(LeanExpr::Const(-1), toggle_interp),
    ));

    // C2 continuity: Nxt(current) − Loc(next); C3 copy-forward: Nxt(acc) − Loc(running).
    let continuity = window_gate(NEXT, CURRENT); // Nxt(CURRENT) − Loc(NEXT)
    let copy_forward = window_gate(RUNNING_HASH, ACC); // Nxt(ACC) − Loc(RUNNING_HASH)

    EffectVmDescriptor2 {
        name: "dfa-routing-toggle-2state::poseidon2-v1".to_string(),
        trace_width: DFA_WIDTH,
        public_input_count: 4,
        tables: vec![],
        constraints: vec![
            chip_lookup(
                &[CURRENT, SYMBOL, NEXT, ZERO_LANE],
                ENTRY_HASH,
                ENTRY_LANE_BASE,
            ),
            chip_lookup(&[ACC, ENTRY_HASH], RUNNING_HASH, RUNNING_LANE_BASE),
            g(LeanExpr::Var(ZERO_LANE)),
            is_first_bool,
            state_grid,
            symbol_grid,
            transition,
            continuity,
            copy_forward,
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: CURRENT,
                pi_index: PI_INITIAL,
            }),
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::First,
                body: LeanExpr::add(LeanExpr::Var(IS_FIRST), LeanExpr::Const(-1)),
            }),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: ACC,
                pi_index: PI_TABLE,
            }),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col: NEXT,
                pi_index: PI_FINAL,
            }),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col: RUNNING_HASH,
                pi_index: PI_ROUTE,
            }),
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// A transition `WindowGate` body `Nxt(nxt_col) − Loc(loc_col)`, `on_transition = true`, built via
/// the wire JSON (the `WindowExpr`/`WindowGateSpec` constructors are internal to `descriptor_ir2`;
/// decoding a one-constraint golden is the stable public path to the same value).
fn window_gate(loc_col: usize, nxt_col: usize) -> VmConstraint2 {
    let json = format!(
        r#"{{"name":"w","ir":2,"trace_width":22,"public_input_count":0,"tables":[],"constraints":[{{"t":"window_gate","on_transition":true,"body":{{"t":"add","l":{{"t":"nxt","c":{nxt_col}}},"r":{{"t":"mul","l":{{"t":"const","v":-1}},"r":{{"t":"loc","c":{loc_col}}}}}}}}}],"hash_sites":[],"ranges":[]}}"#
    );
    parse_vm_descriptor2(&json)
        .expect("window-gate golden decodes")
        .constraints[0]
        .clone()
}

// ---------------------------------------------------------------------------
// Honest routing witness (the toggle DFA, `step(s,y) = s XOR y`).
// ---------------------------------------------------------------------------

/// The toggle transition `step(s, y) = s XOR y` over `{0,1}`.
fn step(s: u32, y: u32) -> u32 {
    s ^ y
}

/// Build an honest 4-row routing trace + public inputs from a start state, a symbol at row 0, and a
/// running-hash seed (the "table commitment"). Rows 1..3 self-loop under symbol 0. Fills the entry
/// hash, running-hash chain, and the copy-forward `acc` column (the chip LANE columns 8..21 are left
/// zero — the prover's `trace_with_chip_lanes` fills them from the genuine permutation). Returns
/// `(trace, pis)` with `pis = [initial, final, seed, route_commitment]`.
fn honest_witness(start: u32, sym0: u32, seed: BabyBear) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let n = 4usize;
    let symbols = [sym0, 0, 0, 0];
    let mut cur = start;
    let mut running = seed;
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(n);
    for (i, &sym) in symbols.iter().enumerate() {
        let nxt = step(cur, sym);
        let entry = hash_4_to_1(&[
            BabyBear::new(cur),
            BabyBear::new(sym),
            BabyBear::new(nxt),
            BabyBear::ZERO,
        ]);
        let acc = running; // acc[0] = seed; acc[i] = running[i-1]
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
        row[ZERO_LANE] = BabyBear::ZERO;
        row[ACC] = acc;
        rows.push(row);
        cur = nxt;
    }
    let final_state = BabyBear::new(cur);
    let route = rows[n - 1][RUNNING_HASH];
    let pis = vec![BabyBear::new(start), final_state, seed, route];
    (rows, pis)
}

/// The witness fixture: start at state 0, read symbol 1 (IDLE → toggled), seed the running hash with
/// a distinct felt so any tamper genuinely changes a committed value.
fn fixture() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    honest_witness(0, 1, BabyBear::new(0x51D5))
}

/// A trace that routes 0 --sym1--> 0 (FORBIDDEN; the toggle `step(0,1) = 1`), then self-loops under
/// symbol 0. Every constraint EXCEPT the GAP-A transition `Gate` at row 0 is satisfied (continuity,
/// both chips, the boundaries), so the transition tooth is the sole violated relation. `(trace, pis)`.
fn forbidden_edge_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let seed = BabyBear::new(0x51D5);
    let cur_seq = [0u32, 0, 0, 0];
    let sym_seq = [1u32, 0, 0, 0];
    let next_seq = [0u32, 0, 0, 0]; // row 0 forbidden; rows 1..3 follow step(0,0)=0
    let mut running = seed;
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(4);
    for i in 0..4 {
        let (cur, sym, nxt) = (cur_seq[i], sym_seq[i], next_seq[i]);
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
        trace.push(row);
    }
    let pis = vec![
        BabyBear::new(0),
        BabyBear::new(0), // final = next[3] = 0
        seed,
        trace[3][RUNNING_HASH],
    ];
    (trace, pis)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. Prove-THEN-verify is the
/// faithful gate (in `--release`, `prove_vm_descriptor2` does not self-verify — the CONSUMER's
/// `verify_vm_descriptor2` is the real check, exactly the production posture).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,      // panicked anywhere → rejected
        Ok(Err(_)) => true,  // prove OR verify returned Err → rejected
        Ok(Ok(())) => false, // proved AND verified → ACCEPTED
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin, with the expected shape.
#[test]
fn dfa_routing_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, DFA_WIDTH);
    assert_eq!(decoded.public_input_count, 4);
    assert_eq!(decoded.constraints.len(), 14);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 2, "entry-hash + running-hash chip lookups");
    let window_gates = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(window_gates, 2, "continuity + copy-forward window gates");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 4, "B1 initial · seed acc · B2 final · B3 route");
}

/// STEP 2 — the two chip mappings this family names: an arity-4 absorb IS `hash_4_to_1` (entry
/// hash) and an arity-2 absorb IS `hash_2_to_1` (the running-hash step), each with every input
/// load-bearing.
#[test]
fn dfa_chip_lookups_are_the_named_hashes() {
    // arity-4 entry hash.
    let e = [
        BabyBear::new(0),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::ZERO,
    ];
    assert_eq!(
        chip_absorb_all_lanes(4, &e)[0],
        hash_4_to_1(&e),
        "arity-4 chip out0 must equal hash_4_to_1 (the entry hash)"
    );
    // arity-2 running step.
    let a = BabyBear::new(1234);
    let b = BabyBear::new(5678);
    assert_eq!(
        chip_absorb_all_lanes(2, &[a, b])[0],
        hash_2_to_1(a, b),
        "arity-2 chip out0 must equal hash_2_to_1 (the running-hash step)"
    );
    // both running inputs are load-bearing.
    assert_ne!(hash_2_to_1(a, b), hash_2_to_1(a + BabyBear::ONE, b));
    assert_ne!(hash_2_to_1(a, b), hash_2_to_1(a, b + BabyBear::ONE));
}

/// STEP 3 — THE POSITIVE POLE: an honest routing witness proves through the emitted descriptor and
/// the proof re-verifies against the public `[initial, final, seed, route_commitment]`.
#[test]
fn honest_route_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = fixture();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest routing witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the public inputs");
    // The classification is genuine (final_state = LOCAL/1 after one toggle from 0).
    assert_eq!(pis[PI_FINAL], BabyBear::new(1), "toggled 0 → 1");
    assert_ne!(
        pis[PI_ROUTE],
        BabyBear::ZERO,
        "route commitment is a real hash"
    );
}

/// STEP 4a — MUTATION CANARY (final state): the honest proof, verified with a FORGED `final_state`
/// PI, is refused by the B2 last-row `PiBinding`. Can't claim a classification you didn't reach.
#[test]
fn forged_final_state_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = fixture();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest proves");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("honest verifies — else the canary is vacuous");
    let mut forged = pis.clone();
    forged[PI_FINAL] = BabyBear::new(0); // claim REJECT/0, not the real toggled 1
    assert_ne!(
        forged[PI_FINAL], pis[PI_FINAL],
        "the forged classification differs"
    );
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged final_state must fail the B2 boundary"
    );
}

/// STEP 4b — MUTATION CANARY (route commitment): a forged `route_commitment` PI is refused by the
/// B3 last-row `PiBinding` — the commitment binds the routed trace.
#[test]
fn forged_route_commitment_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = fixture();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest proves");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("honest verifies — else the canary is vacuous");
    let mut forged = pis.clone();
    forged[PI_ROUTE] = pis[PI_ROUTE] + BabyBear::ONE;
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged route_commitment must fail the B3 boundary"
    );
}

/// STEP 4c — MUTATION CANARY (table-commitment seed): a forged `table_commitment` PI is refused by
/// the first-row `acc` `PiBinding` (the chain seed) — a router cannot reuse a route under a
/// different table commitment.
#[test]
fn forged_table_commitment_seed_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = fixture();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest proves");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("honest verifies — else the canary is vacuous");
    let mut forged = pis.clone();
    forged[PI_TABLE] = pis[PI_TABLE] + BabyBear::ONE;
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged table_commitment seed must fail the first-row acc PiBinding"
    );
}

/// STEP 4d — MUTATION CANARY (forbidden edge): an internally-consistent trace that routes a
/// FORBIDDEN edge (`next != step(state, symbol)`) is refused by the GAP-A transition `Gate`. Row 0
/// claims `step(0, 1) = 0` (the real toggle is 1); every other constraint (continuity, both chips,
/// the boundaries) is satisfied, so the transition tooth bites in isolation.
#[test]
fn forbidden_edge_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    // Non-vacuity: the honest (table-following) route is accepted.
    let (honest_trace, honest_pis) = fixture();
    assert!(
        !rejects(&desc, &honest_trace, &honest_pis),
        "honest route must be accepted — else the canary is vacuous"
    );

    let (trace, pis) = forbidden_edge_witness();
    assert!(
        rejects(&desc, &trace, &pis),
        "a forbidden routed edge (next != step) must fail the transition gate"
    );
}

/// LOAD-BEARING PROOF — the forbidden-edge canary bites the GAP-A transition `Gate` SPECIFICALLY:
/// with that single constraint DROPPED from the descriptor, the same forbidden-edge trace (every
/// other relation intact) PROVES AND VERIFIES. So the transition gate is exactly the tooth that
/// refuses a route the table forbids — the canary is not passing for an unrelated reason.
#[test]
fn transition_gate_is_load_bearing() {
    // The transition gate is constraint index 6 (entry, running, zero, is_first, state, symbol, TRANSITION, …).
    let full = hand_built_desc();
    assert!(
        matches!(
            &full.constraints[6],
            VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Add(..)))
        ),
        "index 6 must be the transition gate (next − interpolant)"
    );
    let mut dropped = full.clone();
    dropped.constraints.remove(6);

    let (trace, pis) = forbidden_edge_witness();
    // With the transition gate present, the forbidden edge is refused (the canary).
    assert!(
        rejects(&full, &trace, &pis),
        "gate present ⇒ forbidden edge refused"
    );
    // With ONLY the transition gate dropped, the very same forbidden edge is ACCEPTED — proving the
    // gate alone is what refuses it (every other relation the trace already satisfies).
    assert!(
        !rejects(&dropped, &trace, &pis),
        "gate dropped ⇒ forbidden edge accepted (the transition gate is the load-bearing tooth)"
    );
}

/// STEP 4e — MUTATION CANARY (running hash): the honest trace with a FORGED last-row running hash
/// (and `route_commitment` set to match, so B3 does not pre-empt) is refused by the arity-2 chip
/// `Lookup` — a fabricated commitment step names a chip row no genuine permutation serves.
#[test]
fn forged_running_hash_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (mut trace, pis) = fixture();
    let last = trace.len() - 1;
    // sanity: the honest trace is accepted (non-vacuity).
    assert!(!rejects(&desc, &trace, &pis), "honest must be accepted");
    // Forge the last running hash and point route_commitment at the forgery so ONLY the chip binding
    // (out0 != genuine permutation) is the violated constraint.
    let forged = trace[last][RUNNING_HASH] + BabyBear::ONE;
    trace[last][RUNNING_HASH] = forged;
    let mut forged_pis = pis.clone();
    forged_pis[PI_ROUTE] = forged;
    assert!(
        rejects(&desc, &trace, &forged_pis),
        "a fabricated running hash (unserved chip row) must be REJECTED by the chip lookup"
    );
}
