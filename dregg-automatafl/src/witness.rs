//! # The witness generator for the Lean-emitted automaton-step (D1) descriptor.
//!
//! **This is the trusted, fail-closed trace generator that fills the PROVEN Lean descriptor
//! `automataflStepDescN {n}` (`circuit/descriptors/by-name/automatafl-step-n{n}.json`) — so the
//! deployed automatafl proof proves through the object that was REFINED in Lean, not the
//! hand-authored Rust AIR.** House-law #1: the AIR is authored in Lean; this Rust only fills a
//! trace and CALLS the general IR-v2 prover. It authors no constraints.
//!
//! ## Front-end reuse + tail rewrite (the design, `docs/reference/AUTOMATAFL-WIRING-AND-SHIP`)
//!
//! The Lean layout's columns `0 .. A_BACK_TAIL` are byte-identical to the frozen Rust `Builder`
//! allocation order (`air.rs::build_d1_bound` → `automaton_gadget`): old cells, new cells, the
//! automaton coordinate + its bit ranges, the auto row×column one-hots, the four ray scans, the
//! two `decide_axis` truth tables, `choose_offset`, and the step + board-update gates. So the
//! column VALUES for that prefix transfer DIRECTLY from the existing co-build harness — we run
//! [`crate::air::build_d1_honest`] (which drives [`crate::reference`], the game oracle) and read
//! its filled `values`.
//!
//! The only genuine rewrite is the board-commitment TAIL. Where the Rust AIR appended two
//! `board_root8` Merkle roots (arity-16 Poseidon2 lookups → 8+8 PIs), the Lean descriptor appends
//! `⌈n²/15⌉` **packed base-4 felts per board** (`packed[f] = Σ_{i<15} cell[15f+i]·4^i`), each a
//! degree-1 pack gate riding a first-row `PiBinding`, and NO lookup. We fill those felts from the
//! board cells and drop them in the tail columns.
//!
//! ## The PI vector (the `custom_state_binding` ABI + the packed commitment)
//!
//! ```text
//!   [0  .. 16)          old8 ‖ new8      the CELL state-binding prefix (placeholder here; the
//!                                        fold driver connects it to the leg's real rotated roots)
//!   [16 .. 16+F)        packed_old[F]    F = ⌈n²/15⌉ packed base-4 felts of the OLD board
//!   [16+F .. 16+2F)     packed_new[F]    the claimed-next board's packed felts
//!   [16+2F], [16+2F+1]  ax, ay           the automaton coordinate
//! ```
//!
//! ## Fail-closed
//!
//! A wrong column value makes a descriptor gate UNSAT — [`prove_vm_descriptor2`] refuses it; it
//! never mis-accepts. [`step_trace_accepts`] is the fast in-memory shadow (the real `Ir2Air`
//! row-local evaluator over the decoded descriptor) the tests gate on before the slow prove.

use dregg_circuit::descriptor_ir2::EffectVmDescriptor2;
use dregg_circuit::field::BabyBear;

use crate::air::{build_d1_honest, placeholder_roots};
use crate::reference::{Board, automaton_step};

/// The by-name loader identity of the Lean D1 step descriptor for board size `n`
/// (`descriptor_by_name(&step_descriptor_name(n))`). Emitted for `n ∈ {2, 11}`.
pub fn step_descriptor_name(n: usize) -> String {
    format!("dregg-automatafl-step-d1-n{n}")
}

/// The number of packed base-4 commitment felts per board at size `n`: `⌈n²/15⌉`
/// (15 base-4 cells per felt, `4^15 < BABYBEAR_P < 4^16`).
pub fn packed_felts(n: usize) -> usize {
    let k = n * n;
    k.div_ceil(15)
}

/// The generated single-row trace + public inputs for the Lean D1 descriptor at a board.
#[derive(Clone, Debug)]
pub struct StepTrace {
    /// One trace row of width `descriptor.trace_width`. The descriptor's gates are row-local, so
    /// the base trace is this row replicated to the prover's row count (see [`Self::base_trace`]).
    pub row: Vec<BabyBear>,
    /// The descriptor public inputs (see the module doc's ABI table).
    pub public_inputs: Vec<BabyBear>,
    /// The board size.
    pub n: usize,
}

impl StepTrace {
    /// The base trace for the prover: the row replicated `num_rows` times (row-local gates are
    /// constant across rows, so replication satisfies them identically).
    pub fn base_trace(&self, num_rows: usize) -> Vec<Vec<BabyBear>> {
        vec![self.row.clone(); num_rows.max(1)]
    }
}

/// Pack a board's cells into `⌈n²/15⌉` base-4 felts: `packed[f] = Σ_{i<15} cell[15f+i]·4^i`. The
/// last felt is partial when `n²` is not a multiple of 15. `4^15 - 1 < BABYBEAR_P`, so no felt
/// overflows.
fn pack_board(board: &Board) -> Vec<BabyBear> {
    let k = board.n * board.n;
    let nfelts = packed_felts(board.n);
    (0..nfelts)
        .map(|f| {
            let mut acc: u64 = 0;
            for i in 0..15usize {
                let cell = f * 15 + i;
                if cell < k {
                    acc += (board.cells[cell] as u64) * 4u64.pow(i as u32);
                }
            }
            BabyBear::from_u64(acc)
        })
        .collect()
}

/// **THE WITNESS GENERATOR.** Fill the Lean D1 descriptor's trace for the honest transition
/// `next = automaton_step(old)`: reuse the Rust co-build front-end fill for columns
/// `0 .. A_BACK_TAIL`, rewrite the tail to the packed base-4 board commitment, and assemble the
/// public inputs.
///
/// `desc` is the decoded Lean descriptor for `old.n` (via
/// `dregg_circuit::descriptor_by_name(&step_descriptor_name(old.n))`). The generator is checked
/// against it: on any layout disagreement it returns `Err` (fail-closed) rather than a trace that
/// silently mis-fills.
pub fn automatafl_step_trace(old: &Board, desc: &EffectVmDescriptor2) -> Result<StepTrace, String> {
    let n = old.n;
    let k = n * n;
    let nfelts = packed_felts(n);

    // The descriptor's shape must be the packed-felt D1 layout for this board size.
    let expected_pi = 16 + 2 * nfelts + 2;
    if desc.public_input_count != expected_pi {
        return Err(format!(
            "automatafl witness-gen: descriptor '{}' publishes {} PIs, but board n={n} needs \
             16 (old8‖new8) + 2·{nfelts} (packed) + 2 (ax,ay) = {expected_pi}",
            desc.name, desc.public_input_count
        ));
    }
    // A_BACK_TAIL = trace_width − 2·⌈n²/15⌉ (the front-end + back-end, before the packed tail).
    let front = desc.trace_width.checked_sub(2 * nfelts).ok_or_else(|| {
        format!(
            "automatafl witness-gen: descriptor width {} < packed tail 2·{nfelts}",
            desc.trace_width
        )
    })?;

    // Front-end reuse: the Rust co-build harness fills columns 0..front from the reference oracle.
    let b = build_d1_honest(old);
    if b.width() < front {
        return Err(format!(
            "automatafl witness-gen: co-build harness produced {} columns, fewer than the \
             descriptor front-end width {front}",
            b.width()
        ));
    }
    // The automaton coordinate lives in the front-end at columns 2k, 2k+1 (the `alloc` order:
    // old[k] ‖ new[k] ‖ ax ‖ ay ‖ …). Confirm it sits inside the reused prefix.
    let (ax_col, ay_col) = (2 * k, 2 * k + 1);
    if ay_col >= front {
        return Err(format!(
            "automatafl witness-gen: automaton coord columns ({ax_col},{ay_col}) fall outside the \
             front-end prefix width {front}"
        ));
    }

    let packed_old = pack_board(old);
    let next = automaton_step(old);
    let packed_new = pack_board(&next);

    // Assemble the full-width row: [0..front) from the co-build fill, then the packed tail.
    let mut row = vec![BabyBear::ZERO; desc.trace_width];
    for c in 0..front {
        row[c] = b.value(c);
    }
    for (f, v) in packed_old.iter().enumerate() {
        row[front + f] = *v;
    }
    for (f, v) in packed_new.iter().enumerate() {
        row[front + nfelts + f] = *v;
    }

    // The public inputs: the state-binding prefix (placeholder cell roots, as the Rust D1 path),
    // then the packed board commitments, then the automaton coordinate.
    let (old8, new8) = placeholder_roots();
    let mut public_inputs = Vec::with_capacity(desc.public_input_count);
    public_inputs.extend_from_slice(&old8);
    public_inputs.extend_from_slice(&new8);
    public_inputs.extend_from_slice(&packed_old);
    public_inputs.extend_from_slice(&packed_new);
    public_inputs.push(b.value(ax_col));
    public_inputs.push(b.value(ay_col));
    debug_assert_eq!(public_inputs.len(), desc.public_input_count);

    Ok(StepTrace {
        row,
        public_inputs,
        n,
    })
}

/// The fast in-memory shadow: does the generated trace SATISFY the decoded Lean descriptor?
/// Runs the real `Ir2Air` row-local evaluator (`ir2_eval_accepts`) over the descriptor's gates —
/// the same arithmetization the STARK quotient enforces on the prove path. `true` iff every gate
/// (board range, coordinate ranges, one-hots, ray scans, decide/choose/step, the packed-felt
/// commitment, and the PI bindings) vanishes on the row. This is what the tests gate on before
/// the slow leaf prove; a wrong fill fails here exactly as it would fail the STARK.
pub fn step_trace_accepts(desc: &EffectVmDescriptor2, tr: &StepTrace) -> bool {
    let rows_i64: Vec<Vec<i64>> = tr
        .base_trace(1)
        .iter()
        .map(|r| r.iter().map(|f| f.0 as i64).collect())
        .collect();
    let pis_i64: Vec<i64> = tr.public_inputs.iter().map(|f| f.0 as i64).collect();
    dregg_circuit::descriptor_ir2::ir2_eval_accepts_i64(desc, &rows_i64, &pis_i64)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ATT, AUTO, REP, VAC, stock_two_player};
    use dregg_circuit::descriptor_by_name::descriptor_by_name;

    fn n5_board() -> Board {
        let n = 5usize;
        let mut cells = vec![VAC; n * n];
        cells[4 * n + 2] = ATT;
        cells[2 * n + 2] = AUTO;
        Board {
            n,
            cells,
            auto: (2, 2),
            col_rule: true,
        }
    }

    fn n2_board() -> Board {
        // A minimal n=2 board with the automaton and one repulsor.
        let n = 2usize;
        let mut cells = vec![VAC; n * n];
        cells[0] = AUTO; // (0,0)
        cells[3] = REP; // (1,1)
        Board {
            n,
            cells,
            auto: (0, 0),
            col_rule: true,
        }
    }

    /// The n=11 stock board's honest step trace SATISFIES the Lean-emitted n=11 descriptor —
    /// the front-end reuse + packed-felt tail land byte-compatibly on the PROVEN layout.
    #[test]
    fn n11_stock_trace_satisfies_lean_descriptor() {
        let desc = descriptor_by_name(&step_descriptor_name(11))
            .expect("the n=11 automatafl-step descriptor dispatches by name");
        assert_eq!(desc.trace_width, 678);
        assert_eq!(desc.public_input_count, 36);
        let old = stock_two_player();
        let tr = automatafl_step_trace(&old, &desc).expect("witness-gen fills the n=11 layout");
        assert_eq!(tr.row.len(), desc.trace_width);
        assert!(
            step_trace_accepts(&desc, &tr),
            "the generated n=11 trace must satisfy every gate of the PROVEN Lean descriptor"
        );
    }

    /// The step trace over a chain of stepped boards (the deployed match's per-turn leaves) all
    /// satisfy the descriptor — not just the opening position.
    #[test]
    fn n11_stepped_chain_all_satisfy() {
        let desc = descriptor_by_name(&step_descriptor_name(11)).unwrap();
        let mut board = stock_two_player();
        for turn in 0..4 {
            let tr = automatafl_step_trace(&board, &desc)
                .unwrap_or_else(|e| panic!("turn {turn} witness-gen: {e}"));
            assert!(
                step_trace_accepts(&desc, &tr),
                "turn {turn}: the stepped board's trace must satisfy the Lean descriptor"
            );
            board = automaton_step(&board);
        }
    }

    /// The n=2 minimal instance likewise satisfies its Lean descriptor (254w/20pi).
    #[test]
    fn n2_trace_satisfies_lean_descriptor() {
        let desc = descriptor_by_name(&step_descriptor_name(2))
            .expect("the n=2 automatafl-step descriptor dispatches by name");
        assert_eq!(desc.trace_width, 254);
        assert_eq!(desc.public_input_count, 20);
        let old = n2_board();
        let tr = automatafl_step_trace(&old, &desc).expect("witness-gen fills the n=2 layout");
        assert!(
            step_trace_accepts(&desc, &tr),
            "the generated n=2 trace must satisfy the PROVEN Lean descriptor"
        );
    }

    /// TAMPER REJECTS: a single corrupted board cell (breaking the packed commitment and the
    /// downstream reads) makes the descriptor UNSAT — the fail-closed property.
    #[test]
    fn tampered_tail_is_rejected() {
        let desc = descriptor_by_name(&step_descriptor_name(11)).unwrap();
        let old = stock_two_player();
        let mut tr = automatafl_step_trace(&old, &desc).unwrap();
        // Corrupt a packed OLD felt (the tail) without touching its board cells: the pack gate
        // `packed - Σ cell·4^i == 0` no longer vanishes.
        let front = desc.trace_width - 2 * packed_felts(11);
        tr.row[front] += BabyBear::ONE;
        assert!(
            !step_trace_accepts(&desc, &tr),
            "a corrupted packed-felt column must fail the descriptor's pack gate"
        );
    }

    /// The n=5 deployed TEST board size has NO emitted Lean descriptor (only n=2, n=11 are pinned)
    /// — the witness-gen path is correctly BLOCKED there, fail-closed, not silently mis-filled.
    #[test]
    fn n5_has_no_descriptor_blocked_not_faked() {
        assert!(
            descriptor_by_name(&step_descriptor_name(5)).is_none(),
            "n=5 is not an emitted Lean descriptor size; the loader must return None (blocked)"
        );
        // And the board still steps fine via the reference oracle — only the Lean-descriptor
        // route is unavailable at n=5.
        let _ = automaton_step(&n5_board());
    }
}
