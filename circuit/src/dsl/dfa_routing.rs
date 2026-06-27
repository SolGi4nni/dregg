//! `dregg-dfa-routing-v1`: DFA message-routing classification proven in circuit,
//! with the route decision **bound to a running-hash route commitment**.
//!
//! This is the DSL-native, production form of the standalone AIR exercised in
//! `dregg-tests/src/dfa_circuit.rs`. It is faithful to the Lean model
//! `Dregg2.Crypto.DfaAcceptanceAir` (the authoritative algebraic statement): a
//! trace that satisfies this descriptor IS the deterministic run of the routing
//! DFA on its symbol sequence, and its public `route_commitment` is the rolling
//! Poseidon2 hash `compress (… compress (compress tableCommitment entry₀) entry₁ …)`
//! over the whole transition trace. Two traces with the same `table_commitment`
//! and the same `route_commitment` have identical entry-hash chains (the Lean
//! `route_commitment_binds_trace` pivot under Poseidon2 collision-resistance), so
//! **a router cannot claim a delivery/classification it did not make**: the
//! commitment binds the exact `(state, symbol, next)` chain it routed.
//!
//! # Why this descriptor (and not the generic DFA lookup)
//!
//! `dsl::circuit`'s test `dfa_lookup_descriptor` (one `Lookup` constraint) proves
//! only "every row is a valid transition" — it leaves the Lean model's GAP-B open:
//! there is no rolling commitment tying the trace to the table commitment and the
//! claimed final state, so nothing distinguishes one accepted route from another
//! and nothing pins the route to a public commitment. This descriptor closes
//! GAP-B with the entry-hash chain (`Hash4to1` C1), the cross-row running-hash
//! accumulation (`ChainedHash2to1` C3), the PI-seeded chain seed (`SeedHash2to1`,
//! the Lean `seed` conjunct that ties the chain to the *table* commitment), and
//! the three boundaries B1/B2/B3 binding `initial_state` / `final_state` /
//! `route_commitment` to public inputs.
//!
//! # Live wiring
//!
//! The descriptor deploys as a `CellProgram`; its `vk_hash` is the `commitment`
//! the relay-operator template's `Witnessed { Dfa }` caveat carries (the relay's
//! `route_table_root`). [`prove_dfa_routing_wire`] produces bytes that verify
//! under `turn::executor::membership_verifier::DslCircuitDfaVerifier` (which calls
//! `CellProgram::verify_transition` → `crate::stark::verify`), so the relay's
//! routing decision is gated by a STARK that binds the route commitment.
//!
//! # Trace layout (5 substantive columns + selector + zero lane)
//!
//! | 0 current_state | 1 symbol | 2 next_state | 3 entry_hash | 4 running_hash | 5 is_first | 6 zero |
//!
//! Mirrors `dfa_circuit.rs` `[current_state, symbol, next_state, table_entry_hash,
//! running_hash]` (and Lean `Row`), adding a first-row selector (gates the seed)
//! and a fixed-zero lane (the 4th input to the 4-arity entry hash).
//!
//! # Public-input layout
//!
//! - pi[0]: `initial_state`     (B1: first row `current_state`)
//! - pi[1]: `final_state` (= S) (B2: last row `next_state` — the classification)
//! - pi[2]: `table_commitment`  (the DFA table root, seed of the running hash)
//! - pi[3]: `route_commitment` (= C) (B3: last row `running_hash` — the binding)

use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Column / public-input indices
// ============================================================================

/// Column indices for the routing trace (`dfa_circuit.rs` `COL_*`, plus aux).
pub mod col {
    /// `current_state` — the DFA state entering this step.
    pub const CURRENT_STATE: usize = 0;
    /// `symbol` — the input byte/category read at this step.
    pub const SYMBOL: usize = 1;
    /// `next_state` — the DFA state after this step.
    pub const NEXT_STATE: usize = 2;
    /// `table_entry_hash` — `hash_4_to_1(current, symbol, next, 0)`.
    pub const ENTRY_HASH: usize = 3;
    /// `running_hash` — the rolling route commitment up to and including this row.
    pub const RUNNING_HASH: usize = 4;
    /// First-row selector: 1 at row 0 (gates the seed), 0 elsewhere.
    pub const IS_FIRST: usize = 5;
    /// Fixed-zero lane: the 4th input to the 4-arity entry hash (the padding lane).
    pub const ZERO_LANE: usize = 6;
}

/// Public-input indices (`dfa_circuit.rs` `PI_*`).
pub mod pi {
    /// `initial_state` (B1).
    pub const INITIAL_STATE: usize = 0;
    /// `final_state` S (B2).
    pub const FINAL_STATE: usize = 1;
    /// `table_commitment` C_table (the running-hash seed).
    pub const TABLE_COMMITMENT: usize = 2;
    /// `route_commitment` C (B3).
    pub const ROUTE_COMMITMENT: usize = 3;
}

/// Trace width: 5 substantive columns + first-row selector + zero lane.
pub const DFA_ROUTING_WIDTH: usize = 7;

/// Number of public inputs.
pub const DFA_ROUTING_PI_COUNT: usize = 4;

// ============================================================================
// Descriptor
// ============================================================================

/// Build the `dregg-dfa-routing-v1` circuit descriptor for a transition table.
///
/// `transitions` is the flat `(state, symbol, next)` relation (the same triples
/// `compute_dfa_table_commitment` hashes in `dfa_circuit.rs`); it becomes the
/// transition relation the TABLE constraint enforces. The descriptor binds, per
/// the Lean model:
///
/// - **C1** entry hash: `entry_hash == hash_4_to_1(current, symbol, next, 0)`.
/// - **TABLE** (GAP-A): `next == step(current, symbol)` via a bivariate-interpolation
///   `TableFunction`, plus range constraints pinning `current`/`symbol` to the grid.
/// - **C2** continuity: `next_row.current_state == this_row.next_state`.
/// - **C3** accumulation: `next_row.running == hash_2_to_1(this_row.running, next_row.entry_hash)`.
/// - **seed** (row 0): `running₀ == hash_2_to_1(table_commitment, entry₀)`.
/// - **B1/B2/B3**: bind `initial_state` / `final_state` / `route_commitment` to PI.
///
/// `transitions` must be a *total deterministic* function over its grid (every
/// `(state, symbol)` from the distinct values present appears exactly once), which
/// `dfa_circuit.rs`'s `TRANSITIONS` table is. `name` lets callers deploy distinct
/// programs (distinct `vk_hash`) per policy; the AIR identity is always
/// `dregg-dfa-routing-v1` for transcript domain separation.
pub fn dfa_routing_descriptor(name: &str, transitions: &[(u32, u32, u32)]) -> CircuitDescriptor {
    let column = |name: &str, index: usize, kind: ColumnKind| ColumnDef {
        name: name.to_string(),
        index,
        kind,
    };

    // Derive the transition-function grid (distinct, sorted states/symbols) and the
    // row-major output table the `TableFunction` interpolates.
    let (a_values, b_values, outputs) = transition_grid(transitions);

    let constraints = vec![
        // C1 — entry hash binds (current, symbol, next, 0).
        ConstraintExpr::Hash4to1 {
            output_col: col::ENTRY_HASH,
            input_cols: [
                col::CURRENT_STATE,
                col::SYMBOL,
                col::NEXT_STATE,
                col::ZERO_LANE,
            ],
        },
        // The 4th hash lane is the fixed-zero padding lane (matches `BabyBear::ZERO`
        // in `dfa_circuit.rs`); enforce `zero_lane == 0` on every row.
        ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::ZERO_LANE],
            }],
        },
        // The first-row selector is boolean.
        ConstraintExpr::Binary { col: col::IS_FIRST },
        // TABLE range: current_state is on the state grid (∏ (state - sᵢ) == 0). Pins
        // the `TableFunction` input so off-grid rows cannot escape interpolation.
        vanishing_on_grid(col::CURRENT_STATE, &a_values),
        // TABLE range: symbol is on the symbol grid.
        vanishing_on_grid(col::SYMBOL, &b_values),
        // TABLE (GAP-A): next_state == step(current_state, symbol).
        ConstraintExpr::TableFunction {
            a_col: col::CURRENT_STATE,
            b_col: col::SYMBOL,
            out_col: col::NEXT_STATE,
            a_values: a_values.clone(),
            b_values: b_values.clone(),
            outputs,
        },
        // C2 — continuity: next row's current_state == this row's next_state.
        ConstraintExpr::Transition {
            next_col: col::CURRENT_STATE,
            local_col: col::NEXT_STATE,
        },
        // C3 — running-hash accumulation: next.running == hash(this.running, next.entry).
        ConstraintExpr::ChainedHash2to1 {
            output_next_col: col::RUNNING_HASH,
            seed_local_col: col::RUNNING_HASH,
            input_next_col: col::ENTRY_HASH,
        },
        // seed — row 0: running₀ == hash(table_commitment, entry₀). Gated on is_first
        // so it fires only on the seed row (boundary-pinned to 1 there).
        ConstraintExpr::Gated {
            selector_col: col::IS_FIRST,
            inner: Box::new(ConstraintExpr::SeedHash2to1 {
                output_col: col::RUNNING_HASH,
                seed_pi_index: pi::TABLE_COMMITMENT,
                input_col: col::ENTRY_HASH,
            }),
        },
    ];

    // The TableFunction is degree (|states|-1)+(|symbols|-1); the grid-range
    // vanishing polynomials are degree |states| / |symbols|. The blowup-driving
    // degree is the max of those.
    let table_degree = a_values.len().saturating_sub(1) + b_values.len().saturating_sub(1);
    let range_degree = a_values.len().max(b_values.len());
    let max_degree = table_degree.max(range_degree).max(2);

    let boundaries = vec![
        // B1 — first row starts in initial_state.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CURRENT_STATE,
            pi_index: pi::INITIAL_STATE,
        },
        // First-row selector pinned to 1 (forces the seed constraint to fire on row 0).
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::IS_FIRST,
            value: BabyBear::ONE,
        },
        // B2 — last row's next_state is the public final_state S (the classification).
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::NEXT_STATE,
            pi_index: pi::FINAL_STATE,
        },
        // B3 — last row's running_hash is the public route_commitment C.
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::RUNNING_HASH,
            pi_index: pi::ROUTE_COMMITMENT,
        },
    ];

    CircuitDescriptor {
        name: name.to_string(),
        trace_width: DFA_ROUTING_WIDTH,
        max_degree,
        columns: vec![
            column("current_state", col::CURRENT_STATE, ColumnKind::Value),
            column("symbol", col::SYMBOL, ColumnKind::Value),
            column("next_state", col::NEXT_STATE, ColumnKind::Value),
            column("table_entry_hash", col::ENTRY_HASH, ColumnKind::Hash),
            column("running_hash", col::RUNNING_HASH, ColumnKind::Hash),
            column("is_first", col::IS_FIRST, ColumnKind::Selector),
            column("zero_lane", col::ZERO_LANE, ColumnKind::Value),
        ],
        constraints,
        boundaries,
        public_input_count: DFA_ROUTING_PI_COUNT,
        lookup_tables: vec![],
    }
}

/// Derive the transition-function grid from a flat triple list: the sorted distinct
/// `state` values (the `a` axis), the sorted distinct `symbol` values (the `b`
/// axis), and the row-major output table `outputs[i*|b|+j] = step(a_values[i],
/// b_values[j])`. Panics if the table is not a total function over the grid (a
/// `(state, symbol)` cell is missing or duplicated) — `dregg-dfa-routing-v1`'s table
/// is total and deterministic by construction.
fn transition_grid(transitions: &[(u32, u32, u32)]) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let mut a_values: Vec<u32> = transitions.iter().map(|(s, _, _)| *s).collect();
    a_values.sort_unstable();
    a_values.dedup();
    let mut b_values: Vec<u32> = transitions.iter().map(|(_, y, _)| *y).collect();
    b_values.sort_unstable();
    b_values.dedup();

    let nb = b_values.len();
    let mut outputs = vec![None; a_values.len() * nb];
    for &(s, y, n) in transitions {
        let i = a_values.binary_search(&s).expect("state in grid");
        let j = b_values.binary_search(&y).expect("symbol in grid");
        let cell = &mut outputs[i * nb + j];
        assert!(
            cell.is_none(),
            "transition table is non-deterministic at ({s}, {y})"
        );
        *cell = Some(n);
    }
    let outputs: Vec<u32> = outputs
        .into_iter()
        .map(|c| c.expect("transition table must be total over its grid"))
        .collect();
    (a_values, b_values, outputs)
}

/// Build the range constraint pinning column `col` to the grid `values`:
/// `∏_{v ∈ values} (col - v) == 0`. Expanded into monomial `PolyTerm`s over the
/// repeated column index (degree `|values|`). At trace rows this forces grid
/// membership, so the `TableFunction` interpolation is evaluated only at real grid
/// points (off-grid escapes are impossible).
fn vanishing_on_grid(col: usize, values: &[u32]) -> ConstraintExpr {
    // Expand ∏ (x - v) into coefficients [c_0, c_1, ..., c_d] (ascending degree).
    // Start with the constant polynomial 1.
    let mut coeffs: Vec<i128> = vec![1];
    for &v in values {
        // Multiply current polynomial by (x - v).
        let mut next = vec![0i128; coeffs.len() + 1];
        for (k, &c) in coeffs.iter().enumerate() {
            next[k + 1] += c; // x * c_k
            next[k] -= c * v as i128; // -v * c_k
        }
        coeffs = next;
    }
    // Emit one PolyTerm per nonzero coefficient: c_k * x^k = c_k * ∏ (k copies of col).
    let terms: Vec<PolyTerm> = coeffs
        .iter()
        .enumerate()
        .filter(|(_, c)| **c != 0)
        .map(|(k, &c)| PolyTerm {
            coeff: int_to_field(c),
            col_indices: vec![col; k],
        })
        .collect();
    ConstraintExpr::Polynomial { terms }
}

/// Reduce a signed integer coefficient into BabyBear (handles negatives via the
/// field modulus).
fn int_to_field(c: i128) -> BabyBear {
    let p = BABYBEAR_P as i128;
    let r = ((c % p) + p) % p;
    BabyBear::new(r as u32)
}

/// Create a `DslCircuit` from a routing descriptor.
pub fn dfa_routing_circuit(name: &str, transitions: &[(u32, u32, u32)]) -> DslCircuit {
    DslCircuit::new(dfa_routing_descriptor(name, transitions))
}

// ============================================================================
// Table commitment
// ============================================================================

/// Compute the DFA transition-table commitment exactly as `dfa_circuit.rs`
/// `compute_dfa_table_commitment` does: each `(state, symbol, next)` triple is
/// hashed `hash_4_to_1(state, symbol, next, 0)`, the entries are grouped into
/// 4-ary Merkle levels, and the single root is the commitment. `transitions` must
/// have a length that the 4-ary tree consumes cleanly (the router uses 16 entries
/// → two levels). The commitment is the running-hash seed (pi[2]).
pub fn compute_table_commitment(transitions: &[(u32, u32, u32)]) -> BabyBear {
    let mut level: Vec<BabyBear> = transitions
        .iter()
        .map(|(s, y, n)| {
            hash_4_to_1(&[
                BabyBear::new(*s),
                BabyBear::new(*y),
                BabyBear::new(*n),
                BabyBear::ZERO,
            ])
        })
        .collect();
    assert!(!level.is_empty(), "transition table must be non-empty");
    while level.len() > 1 {
        assert!(
            level.len().is_multiple_of(4),
            "transition-table commitment needs a 4-ary-clean entry count (got {})",
            level.len()
        );
        level = level
            .chunks(4)
            .map(|c| hash_4_to_1(&[c[0], c[1], c[2], c[3]]))
            .collect();
    }
    level[0]
}

// ============================================================================
// Trace generation
// ============================================================================

/// Witness column map (keyed by column name) paired with public inputs.
type RoutingWitness = (
    std::collections::HashMap<String, Vec<BabyBear>>,
    Vec<BabyBear>,
);

/// Build a routing trace + public inputs from a transition table, a start state,
/// and an input symbol sequence — the DSL form of `dfa_circuit.rs` `build_dfa_trace`.
///
/// The running hash is seeded with the table commitment and folded with each
/// entry hash; the trace is padded to a power of two (≥ 2) with self-loops in the
/// final state. Returns the witness column map (keyed by column name, for
/// `CellProgram::generate_trace`/`prove_transition`) and the public inputs
/// `[initial_state, final_state, table_commitment, route_commitment]`.
///
/// Returns `None` if a `(state, symbol)` pair has no transition in `transitions`
/// (an undefined step — there is no valid route to prove).
pub fn build_routing_witness(
    transitions: &[(u32, u32, u32)],
    start_state: u32,
    symbols: &[u32],
) -> Option<RoutingWitness> {
    assert!(!symbols.is_empty(), "need at least one symbol");
    let step = |s: u32, y: u32| -> Option<u32> {
        transitions
            .iter()
            .find(|(ts, ty, _)| *ts == s && *ty == y)
            .map(|(_, _, tn)| *tn)
    };

    let table_commitment = compute_table_commitment(transitions);
    let n = symbols.len().next_power_of_two().max(2);

    let mut current_states = Vec::with_capacity(n);
    let mut syms = Vec::with_capacity(n);
    let mut next_states = Vec::with_capacity(n);
    let mut entry_hashes = Vec::with_capacity(n);
    let mut running_hashes = Vec::with_capacity(n);

    let mut current = start_state;
    let mut running = table_commitment;

    for &symbol in symbols {
        let next = step(current, symbol)?;
        let entry = hash_4_to_1(&[
            BabyBear::new(current),
            BabyBear::new(symbol),
            BabyBear::new(next),
            BabyBear::ZERO,
        ]);
        running = hash_2_to_1(running, entry);
        current_states.push(BabyBear::new(current));
        syms.push(BabyBear::new(symbol));
        next_states.push(BabyBear::new(next));
        entry_hashes.push(entry);
        running_hashes.push(running);
        current = next;
    }

    let final_state = current;

    // Pad with self-loops in the final state (matches `build_dfa_trace`).
    for _ in symbols.len()..n {
        let pad_symbol = 0u32;
        let pad_next = step(final_state, pad_symbol)?;
        let entry = hash_4_to_1(&[
            BabyBear::new(final_state),
            BabyBear::new(pad_symbol),
            BabyBear::new(pad_next),
            BabyBear::ZERO,
        ]);
        running = hash_2_to_1(running, entry);
        current_states.push(BabyBear::new(final_state));
        syms.push(BabyBear::new(pad_symbol));
        next_states.push(BabyBear::new(pad_next));
        entry_hashes.push(entry);
        running_hashes.push(running);
    }

    let mut is_first = vec![BabyBear::ZERO; n];
    is_first[0] = BabyBear::ONE;
    let zero_lane = vec![BabyBear::ZERO; n];

    let last_next = *next_states.last().unwrap();
    let last_running = *running_hashes.last().unwrap();

    let mut witness = std::collections::HashMap::new();
    witness.insert("current_state".to_string(), current_states);
    witness.insert("symbol".to_string(), syms);
    witness.insert("next_state".to_string(), next_states);
    witness.insert("table_entry_hash".to_string(), entry_hashes);
    witness.insert("running_hash".to_string(), running_hashes);
    witness.insert("is_first".to_string(), is_first);
    witness.insert("zero_lane".to_string(), zero_lane);

    let public_inputs = vec![
        BabyBear::new(start_state),
        last_next,
        table_commitment,
        last_running,
    ];

    Some((witness, public_inputs))
}

// ============================================================================
// Prove / verify
// ============================================================================

/// Prove a routing classification: build the trace for `symbols` against the
/// transition table and produce a STARK over the `dregg-dfa-routing-v1` AIR.
/// Returns the proof and its public inputs `[initial_state, final_state,
/// table_commitment, route_commitment]`.
pub fn prove_dfa_routing(
    name: &str,
    transitions: &[(u32, u32, u32)],
    start_state: u32,
    symbols: &[u32],
) -> Option<(StarkProof, Vec<BabyBear>)> {
    let (witness, public_inputs) = build_routing_witness(transitions, start_state, symbols)?;
    let descriptor = dfa_routing_descriptor(name, transitions);
    let n = witness.get("current_state").map(|v| v.len()).unwrap_or(0);
    let circuit = DslCircuit::new(descriptor.clone());
    let trace = build_trace_from_witness(&descriptor, &witness, n)?;
    let proof = stark::try_prove(&circuit, &trace, &public_inputs).ok()?;
    Some((proof, public_inputs))
}

/// Verify a routing-classification proof against the descriptor and public inputs.
pub fn verify_dfa_routing(
    name: &str,
    transitions: &[(u32, u32, u32)],
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let circuit = dfa_routing_circuit(name, transitions);
    stark::verify(&circuit, proof, public_inputs).map_err(|e| format!("{e:?}"))
}

/// Assemble a row-major trace from the witness column map (name → per-row values),
/// in column-index order. Mirrors `CellProgram::generate_trace` without needing a
/// `CellProgram` wrapper.
fn build_trace_from_witness(
    descriptor: &CircuitDescriptor,
    witness: &std::collections::HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
) -> Option<Vec<Vec<BabyBear>>> {
    if num_rows < 2 || !num_rows.is_power_of_two() {
        return None;
    }
    let mut trace = Vec::with_capacity(num_rows);
    for row_idx in 0..num_rows {
        let mut row = vec![BabyBear::ZERO; descriptor.trace_width];
        for col_def in &descriptor.columns {
            if let Some(values) = witness.get(&col_def.name) {
                if values.len() != num_rows {
                    return None;
                }
                row[col_def.index] = values[row_idx];
            }
        }
        trace.push(row);
    }
    Some(trace)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The EXACT `dregg-dfa-routing-v1` 4-state router (`dfa_circuit.rs:56`):
    /// states IDLE=0, LOCAL=1, REMOTE=2, REJECT=3; symbols internal=0, external=1,
    /// privileged=2, unknown=3. Flattened `(state, symbol, next)` triples.
    fn router_transitions() -> Vec<(u32, u32, u32)> {
        // TRANSITIONS = [[1,2,1,3],[1,2,1,3],[1,2,3,3],[3,3,3,3]]
        let table = [[1, 2, 1, 3], [1, 2, 1, 3], [1, 2, 3, 3], [3, 3, 3, 3]];
        let mut out = Vec::new();
        for (state, row) in table.iter().enumerate() {
            for (symbol, &next) in row.iter().enumerate() {
                out.push((state as u32, symbol as u32, next));
            }
        }
        out
    }

    const NAME: &str = "dregg-dfa-routing-v1";

    /// TOOTH (valid admits): an accepting route verifies, and its public
    /// `route_commitment`/`final_state` are bound by the proof.
    #[test]
    fn correct_route_verifies_and_binds_commitment() {
        let transitions = router_transitions();
        // internal, external, internal: IDLE -> LOCAL -> REMOTE -> LOCAL.
        let (proof, pi) = prove_dfa_routing(NAME, &transitions, 0, &[0, 1, 0])
            .expect("accepting route must be provable");

        // Final state is LOCAL=1 (the genuine classification).
        assert_eq!(pi[pi::FINAL_STATE], BabyBear::new(1), "classified to LOCAL");
        // The route commitment is the running hash (non-trivial binding value).
        assert_ne!(
            pi[pi::ROUTE_COMMITMENT],
            BabyBear::ZERO,
            "route commitment must be a real running hash"
        );

        verify_dfa_routing(NAME, &transitions, &proof, &pi)
            .expect("a correct route must verify against its route_commitment");
    }

    /// TOOTH (forged final state rejected): a router that claims a delivery it did
    /// not make — substituting a different `final_state` in the public inputs while
    /// keeping the honest proof — is rejected by the B2 boundary. This is the core
    /// "can't claim a route you didn't make" guarantee.
    #[test]
    fn forged_final_state_is_rejected() {
        let transitions = router_transitions();
        let (proof, pi) = prove_dfa_routing(NAME, &transitions, 0, &[0, 1, 0])
            .expect("accepting route must be provable");

        // Claim REJECT=3 instead of the real LOCAL=1.
        let mut forged = pi.clone();
        forged[pi::FINAL_STATE] = BabyBear::new(3);
        assert!(
            verify_dfa_routing(NAME, &transitions, &proof, &forged).is_err(),
            "a forged final_state must fail the B2 boundary"
        );
    }

    /// TOOTH (forged route commitment rejected): substituting a different
    /// `route_commitment` fails the B3 boundary — the commitment binds the trace.
    #[test]
    fn forged_route_commitment_is_rejected() {
        let transitions = router_transitions();
        let (proof, pi) = prove_dfa_routing(NAME, &transitions, 0, &[0, 1, 0])
            .expect("accepting route must be provable");

        let mut forged = pi.clone();
        forged[pi::ROUTE_COMMITMENT] = BabyBear::new(0xDEAD);
        assert!(
            verify_dfa_routing(NAME, &transitions, &proof, &forged).is_err(),
            "a forged route_commitment must fail the B3 boundary"
        );
    }

    /// TOOTH (forged table commitment rejected): the running-hash seed is the table
    /// commitment (pi[2]); claiming a different table while presenting the same
    /// proof breaks the seed constraint's PI binding and the route commitment no
    /// longer matches — a router cannot reuse a route under a different table.
    #[test]
    fn forged_table_commitment_is_rejected() {
        let transitions = router_transitions();
        let (proof, pi) = prove_dfa_routing(NAME, &transitions, 0, &[0, 1, 0])
            .expect("accepting route must be provable");

        let mut forged = pi.clone();
        forged[pi::TABLE_COMMITMENT] = BabyBear::new(0xBAD);
        assert!(
            verify_dfa_routing(NAME, &transitions, &proof, &forged).is_err(),
            "a forged table_commitment must fail the seed PI binding"
        );
    }

    /// TOOTH (a REJECT route is classified to REJECT, not LOCAL): a `[unknown, …]`
    /// input lands in REJECT=3 and the proof's final_state is provably REJECT — a
    /// rejecting message cannot present a LOCAL classification.
    #[test]
    fn rejecting_input_classifies_reject_not_local() {
        let transitions = router_transitions();
        // unknown, internal, external: IDLE -> REJECT (absorbing) -> REJECT -> REJECT.
        let (proof, pi) = prove_dfa_routing(NAME, &transitions, 0, &[3, 0, 1])
            .expect("rejecting route is still a valid (provable) DFA run");
        assert_eq!(
            pi[pi::FINAL_STATE],
            BabyBear::new(3),
            "rejecting input classifies to REJECT=3, not LOCAL=1"
        );
        assert_ne!(pi[pi::FINAL_STATE], BabyBear::new(1), "REJECT ≠ LOCAL");
        verify_dfa_routing(NAME, &transitions, &proof, &pi)
            .expect("the honest REJECT route verifies (to REJECT, not LOCAL)");
    }

    /// TOOTH (route commitment binds the trace): two DIFFERENT input sequences yield
    /// DIFFERENT route commitments — the commitment discriminates the routed trace
    /// (the empirical shadow of the Lean `route_commitment_binds_trace`).
    #[test]
    fn distinct_routes_have_distinct_commitments() {
        let transitions = router_transitions();
        let (_p1, pi1) =
            prove_dfa_routing(NAME, &transitions, 0, &[0, 1, 0]).expect("route 1 provable");
        let (_p2, pi2) =
            prove_dfa_routing(NAME, &transitions, 0, &[1, 0, 1]).expect("route 2 provable");
        assert_ne!(
            pi1[pi::ROUTE_COMMITMENT],
            pi2[pi::ROUTE_COMMITMENT],
            "distinct routed traces must have distinct route commitments"
        );
    }

    /// The descriptor validates for deployment as a `CellProgram`.
    #[test]
    fn descriptor_is_deployable() {
        let descriptor = dfa_routing_descriptor(NAME, &router_transitions());
        descriptor
            .validate()
            .expect("dregg-dfa-routing-v1 descriptor must be deployable");
    }

    /// TOOTH (a tampered transition is rejected): a trace row asserting an invalid
    /// `(state, symbol, next)` (next ≠ step(state, symbol)) fails the TableFunction /
    /// entry-hash constraints at prove time — a router cannot route along an edge the
    /// table forbids.
    #[test]
    fn tampered_transition_fails_proving() {
        let transitions = router_transitions();
        let (mut witness, public_inputs) =
            build_routing_witness(&transitions, 0, &[0, 1, 0]).expect("honest witness builds");

        // Tamper: claim row 1's next_state is LOCAL=1 instead of the real REMOTE=2.
        // (IDLE-internal->LOCAL, then LOCAL-external-> should be REMOTE=2.) The
        // TableFunction (next == step(state,symbol)) and the entry hash both reject
        // this fabricated edge.
        if let Some(next_states) = witness.get_mut("next_state") {
            next_states[1] = BabyBear::new(1);
        }
        let descriptor = dfa_routing_descriptor(NAME, &transitions);
        let circuit = DslCircuit::new(descriptor.clone());
        let n = witness.get("current_state").map(|v| v.len()).unwrap_or(0);
        let trace = build_trace_from_witness(&descriptor, &witness, n).expect("trace assembles");
        assert!(
            stark::try_prove(&circuit, &trace, &public_inputs).is_err(),
            "a fabricated transition edge must fail to prove"
        );
    }
}
