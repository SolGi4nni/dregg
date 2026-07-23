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
//!   [16+2F], [16+2F+1]  ax, ay           the CONSUMED (pre-step) automaton coordinate
//!   [16+2F+2], [+3]     nax, nay         the PRODUCED (post-step) automaton coordinate — the
//!                                        fold OUT window's `auto_out`
//! ```
//!
//! `nax`/`nay` are pinned by the Lean-emitted DEGREE-2 gates `nax − ax − m·ox == 0`,
//! `nay − ay − m·oy == 0`, where `m` is the step block's own move mask. The mask is what makes the
//! published coordinate the reference's post-step position on BOTH branches of
//! `automaton_step`'s guard (`m·ox` collapses when the guard refuses), which is what lets the Lean
//! transport be stated against the full `automatonStepCfg` semantics instead of against the column
//! expression `ax + ox`. This generator never re-derives that rule; it SOLVES the emitted gate.
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
    let nfelts = packed_felts(n);

    // THE SHAPE-INDEPENDENT ABI READ. The descriptor's OWN first-row `PiBinding`s say which
    // column every published PI is. Reading them (instead of computing `front = trace_width −
    // 2F`) is what survives the APPEND-ONLY descriptor growth the two-leg fold rides: Leg A's
    // stepped automaton coordinate (`NAX`/`NAY`) is two appended columns + two appended PIs past
    // 35, which the old arithmetic silently mis-aimed. `0..35` are never re-indexed (the capstone
    // quotes absolute indices), so the pinned prefix reads identically at any descriptor version.
    let binds = pi_binding_cols(desc);
    let min_pi = 16 + 2 * nfelts + 2;
    if desc.public_input_count < min_pi {
        return Err(format!(
            "automatafl witness-gen: descriptor '{}' publishes {} PIs, but board n={n} needs at \
             least 16 (old8‖new8) + 2·{nfelts} (packed) + 2 (ax,ay) = {min_pi}",
            desc.name, desc.public_input_count
        ));
    }
    let col_of = |pi: usize| -> Result<usize, String> {
        binds.get(&pi).copied().ok_or_else(|| {
            format!(
                "automatafl witness-gen: descriptor '{}' has no first-row PI binding for PI {pi} \
                 — the packed-felt ABI is not the shape this descriptor publishes",
                desc.name
            )
        })
    };
    let pack_old_col = col_of(16)?;
    let pack_new_col = col_of(16 + nfelts)?;
    if pack_new_col != pack_old_col + nfelts {
        return Err(format!(
            "automatafl witness-gen: the packed tail is not contiguous (pack_old at col \
             {pack_old_col}, pack_new at col {pack_new_col}, F = {nfelts})"
        ));
    }
    // Everything below the packed tail is the front-end the Rust co-build harness fills.
    let front = pack_old_col;
    let ax_col = col_of(16 + 2 * nfelts)?;
    let ay_col = col_of(16 + 2 * nfelts + 1)?;
    if ax_col >= front || ay_col >= front {
        return Err(format!(
            "automatafl witness-gen: the automaton coord columns ({ax_col},{ay_col}) fall outside \
             the front-end prefix width {front}"
        ));
    }

    // Front-end reuse: the Rust co-build harness fills columns 0..front from the reference oracle.
    let b = build_d1_honest(old);
    if b.width() < front {
        return Err(format!(
            "automatafl witness-gen: co-build harness produced {} columns, fewer than the \
             descriptor front-end width {front}",
            b.width()
        ));
    }

    let packed_old = pack_board(old);
    let next = automaton_step(old);
    let packed_new = pack_board(&next);

    // Assemble the row: [0..front) from the co-build fill, then the packed tail at its BOUND
    // columns; every remaining column is SOLVED from the descriptor's own gates below.
    let mut vals: Vec<Option<BabyBear>> = vec![None; desc.trace_width];
    for c in 0..front {
        vals[c] = Some(b.value(c));
    }
    for (f, v) in packed_old.iter().enumerate() {
        vals[pack_old_col + f] = Some(*v);
    }
    for (f, v) in packed_new.iter().enumerate() {
        vals[pack_new_col + f] = Some(*v);
    }

    // THE APPENDED-COLUMN SOLVE. Any column past the packed tail (today: `NAX`/`NAY`, pinned by
    // the DEGREE-2 mask gates `NAX − AX − M·OX == 0`) is filled by EVALUATING the gate that
    // DEFINES it — never by re-deriving the rule in Rust. Rule L solves a gate that is AFFINE in
    // its single unknown, which the mask pin is (`NAX` has coefficient 1; `M` and `OX` are already
    // resolved front-end columns), so the degree-2 product costs the solver nothing. A column no
    // gate determines is a hard `Err`, not a zero-filled guess that would fail the STARK later.
    loop {
        if !crate::resolve_witness::rule_l_pass(desc, &mut vals)? {
            break;
        }
    }
    let unresolved: Vec<usize> = (0..desc.trace_width)
        .filter(|c| vals[*c].is_none())
        .collect();
    if !unresolved.is_empty() {
        return Err(format!(
            "automatafl witness-gen: {} appended column(s) unresolved after the gate solver \
             reached fixpoint (first: {:?}) — no descriptor gate determines them",
            unresolved.len(),
            &unresolved[..unresolved.len().min(8)]
        ));
    }
    let row: Vec<BabyBear> = vals.into_iter().map(|v| v.expect("all resolved")).collect();

    // The public inputs: the state-binding prefix (placeholder cell roots, as the Rust D1 path —
    // the fold driver overwrites them with the leg's real rotated roots), then EVERY bound PI read
    // off its own column. Unbound lanes exist only in the free 16-felt door.
    let (old8, new8) = placeholder_roots();
    let door: Vec<BabyBear> = old8.iter().chain(new8.iter()).copied().collect();
    let mut public_inputs = Vec::with_capacity(desc.public_input_count);
    for pi in 0..desc.public_input_count {
        match binds.get(&pi) {
            Some(&c) => public_inputs.push(row[c]),
            None => {
                let v = door.get(pi).copied().ok_or_else(|| {
                    format!(
                        "automatafl witness-gen: PI {pi} is neither column-bound nor part of the \
                         16-felt free door — the descriptor publishes a lane the ABI cannot fill"
                    )
                })?;
                public_inputs.push(v);
            }
        }
    }
    debug_assert_eq!(public_inputs.len(), desc.public_input_count);

    Ok(StepTrace {
        row,
        public_inputs,
        n,
    })
}

/// The descriptor's own first-row `PiBinding` map (`pi_index -> trace column`) — the ABI read
/// that keeps this generator shape-independent under APPEND-ONLY descriptor growth.
fn pi_binding_cols(desc: &EffectVmDescriptor2) -> std::collections::BTreeMap<usize, usize> {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    let mut out = std::collections::BTreeMap::new();
    for c in &desc.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col,
            pi_index,
        }) = c
        {
            out.insert(*pi_index, *col);
        }
    }
    out
}

/// The PI index of the leg's packed OLD board window (`pack_in`) — the ABI constant the two-leg
/// fold's IN window starts at. `16` = past the `[old8 ‖ new8]` door.
pub const STEP_PACK_IN_PI: usize = 16;

/// The PI index of the leg's packed NEW board window (`pack_out`) at board size `n`.
pub fn step_pack_out_pi(n: usize) -> usize {
    STEP_PACK_IN_PI + packed_felts(n)
}

/// The PI index of the leg's OLD automaton coordinate (`ax`, `ay` at `+0`, `+1`) at size `n`.
pub fn step_auto_in_pi(n: usize) -> usize {
    STEP_PACK_IN_PI + 2 * packed_felts(n)
}

/// The PI index of the leg's STEPPED automaton coordinate (`NAX`, `NAY`) at size `n` — the
/// APPENDED family (`AutomataflStepEmit`'s degree-2 mask pin `NAX − AX − M·OX == 0`) that makes
/// Leg A's OUT window carry the automaton it produced, not the one it consumed. `None` when the
/// loaded descriptor predates the append (then Leg A has no OUT automaton and cannot carry a
/// board window).
pub fn step_auto_out_pi(n: usize, desc: &EffectVmDescriptor2) -> Option<usize> {
    let base = step_auto_in_pi(n) + 2;
    (desc.public_input_count >= base + 2).then_some(base)
}

/// **LEG A's BOARD WINDOW** — `IN = pack(old) ‖ (ax, ay)`, `OUT = pack(new) ‖ (NAX, NAY)`, the
/// `2·F + 4`-PI declaration the two-leg fold connects.
///
/// The OUT window is NOT contiguous — `pack_out` sits at `[16+F .. 16+2F)` and the stepped
/// automaton at the APPENDED `[16+2F+2 .. 16+2F+4)`, with the *consumed* `ax/ay` in between —
/// which is exactly why the binding is a slice LIST rather than one range.
///
/// `Err` when the loaded descriptor predates the `NAX`/`NAY` append: without a published STEPPED
/// automaton coordinate, Leg A's OUT window would carry the automaton it CONSUMED, and the
/// inter-round carry `A_i.OUT == R_{i+1}.IN` would be a lie. Blocked, not faked.
pub fn step_board_window(
    n: usize,
    desc: &EffectVmDescriptor2,
) -> Result<dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding, String> {
    use dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding;
    let f = packed_felts(n);
    let auto_out = step_auto_out_pi(n, desc).ok_or_else(|| {
        format!(
            "automatafl step descriptor '{}' publishes {} PIs — it carries no STEPPED automaton \
             coordinate (NAX/NAY at PI {}, {}). Leg A cannot declare an OUT window whose automaton \
             is the one it PRODUCED, so the inter-round carry is blocked, not faked.",
            desc.name,
            desc.public_input_count,
            step_auto_in_pi(n) + 2,
            step_auto_in_pi(n) + 3
        )
    })?;
    let b = BoardWindowBinding {
        in_slices: vec![(STEP_PACK_IN_PI, f), (step_auto_in_pi(n), 2)],
        out_slices: vec![(step_pack_out_pi(n), f), (auto_out, 2)],
    };
    if !b.is_well_formed() || desc.public_input_count < b.pi_end() {
        return Err(format!(
            "automatafl step board window {b:?} is not expressible in descriptor '{}' ({} PIs)",
            desc.name, desc.public_input_count
        ));
    }
    Ok(b)
}

/// The fast in-memory shadow: does the generated trace SATISFY the decoded Lean descriptor?
/// Runs the real `Ir2Air` row-local evaluator (`ir2_eval_accepts`) over the descriptor's gates —
/// the same arithmetization the STARK quotient enforces on the prove path. `true` iff every gate
/// (board range, coordinate ranges, one-hots, ray scans, decide/choose/step, the packed-felt
/// commitment, and the PI bindings) vanishes on the row. This is what the tests gate on before
/// the slow leaf prove; a wrong fill fails here exactly as it would fail the STARK.
pub fn step_trace_accepts(desc: &EffectVmDescriptor2, tr: &StepTrace) -> bool {
    // TWO rows, as the resolve shadow: a single replicated row exercises only the first/last-row
    // PI bindings and never the `when_transition` gates.
    let rows_i64: Vec<Vec<i64>> = tr
        .base_trace(2)
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
        // The shape is READ, not pinned to a frozen number: the descriptor grows APPEND-ONLY
        // (the `NAX`/`NAY` stepped-automaton family), and the generator must track it.
        assert!(desc.public_input_count >= 36, "the packed-felt ABI floor");
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
        assert!(desc.public_input_count >= 20, "the packed-felt ABI floor");
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
        // `packed - Σ cell·4^i == 0` no longer vanishes. The column is READ off the descriptor's
        // own PI binding, so the canary survives an append-only layout change.
        let front = *pi_binding_cols(&desc)
            .get(&16)
            .expect("pack_old[0] is PI-bound");
        tr.row[front] += BabyBear::ONE;
        assert!(
            !step_trace_accepts(&desc, &tr),
            "a corrupted packed-felt column must fail the descriptor's pack gate"
        );
    }

    /// **`auto_out` IS THE REFERENCE POST-STEP COORDINATE** — the property Leg A's OUT window
    /// needs, checked at every step of a real chain, against the reference oracle. This is the
    /// positive half of the mask-pin story: what the fold reads as `auto_out` is where the
    /// automaton actually stands after the step, and it differs from the coordinate the leg
    /// CONSUMED (so the OUT window is not silently republishing the IN one).
    #[test]
    fn auto_out_is_the_reference_post_step_coordinate_along_a_chain() {
        let desc = descriptor_by_name(&step_descriptor_name(11)).unwrap();
        let auto_in = step_auto_in_pi(11);
        let auto_out = step_auto_out_pi(11, &desc).expect("the descriptor publishes NAX/NAY");
        let mut moved_at_least_once = false;
        // The stock opening (the automaton senses nothing decisive and STANDS STILL — the `m = 0`,
        // zero-offset case) and a pulled position (an attractor 3 north, so the guard FIRES).
        for (name, start) in [("stock", stock_two_player()), ("pulled", pulled_n11())] {
            let mut board = start;
            for turn in 0..4 {
                let tr = automatafl_step_trace(&board, &desc).unwrap();
                assert!(step_trace_accepts(&desc, &tr), "{name} turn {turn}");
                let stepped = automaton_step(&board);
                assert_eq!(
                    (tr.public_inputs[auto_out], tr.public_inputs[auto_out + 1]),
                    (
                        BabyBear::from_u64(stepped.auto.0 as u64),
                        BabyBear::from_u64(stepped.auto.1 as u64)
                    ),
                    "{name} turn {turn}: auto_out must be `automaton_step(old).auto`"
                );
                assert_eq!(
                    (tr.public_inputs[auto_in], tr.public_inputs[auto_in + 1]),
                    (
                        BabyBear::from_u64(board.auto.0 as u64),
                        BabyBear::from_u64(board.auto.1 as u64)
                    ),
                    "{name} turn {turn}: auto_in must be the CONSUMED coordinate"
                );
                if stepped.auto != board.auto {
                    moved_at_least_once = true;
                    assert_ne!(
                        (tr.public_inputs[auto_out], tr.public_inputs[auto_out + 1]),
                        (tr.public_inputs[auto_in], tr.public_inputs[auto_in + 1]),
                        "{name} turn {turn}: on a moved step the two windows must DIFFER"
                    );
                }
                board = stepped;
            }
        }
        assert!(
            moved_at_least_once,
            "the sweep must contain a step that actually moves, or the check is vacuous"
        );
    }

    /// An n=11 position whose automaton IS pulled: an attractor three cells north of it, nothing
    /// else on its cross, so `evaluate_axis` returns `TowardAttractor` and the guard fires.
    fn pulled_n11() -> Board {
        let n = 11usize;
        let mut cells = vec![VAC; n * n];
        cells[5 * n + 5] = AUTO;
        cells[8 * n + 5] = ATT;
        Board {
            n,
            cells,
            auto: (5, 5),
            col_rule: true,
        }
    }

    /// Every `Base(Gate)` body in the descriptor that references column `col`.
    fn gates_touching(
        desc: &EffectVmDescriptor2,
        col: usize,
    ) -> Vec<&dregg_circuit::lean_descriptor_air::LeanExpr> {
        use dregg_circuit::descriptor_ir2::VmConstraint2;
        use dregg_circuit::lean_descriptor_air::VmConstraint;
        desc.constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::Gate(e)) => Some(e),
                _ => None,
            })
            .filter(|e| {
                let mut vars = Vec::new();
                collect_expr_vars(e, &mut vars);
                vars.contains(&col)
            })
            .collect()
    }

    fn collect_expr_vars(e: &dregg_circuit::lean_descriptor_air::LeanExpr, out: &mut Vec<usize>) {
        use dregg_circuit::lean_descriptor_air::LeanExpr;
        match e {
            LeanExpr::Var(i) => {
                if !out.contains(i) {
                    out.push(*i);
                }
            }
            LeanExpr::Const(_) => {}
            LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
                collect_expr_vars(a, out);
                collect_expr_vars(b, out);
            }
        }
    }

    /// **THE MASK-PIN CANARY — the emitted gate is the degree-2 mask form, evaluated.**
    ///
    /// The Lean-emitted pin is `NAX − AX − M·OX == 0`. This test drives the ACTUAL gate body out
    /// of the loaded descriptor and evaluates it on synthetic assignments, so it states what the
    /// wire object forces:
    ///
    /// * `M = 0` (the guard refuses): the gate is satisfied **only** by `NAX = AX`. The retired
    ///   degree-1 pin `NAX − (AX + OX) == 0` forced `NAX = AX + OX` here instead — a value the
    ///   reference automaton does not occupy on that branch.
    /// * `M = 1` (the guard fires): the gate is satisfied **only** by `NAX = AX + OX`.
    ///
    /// Together those are exactly `if m = 1 then ax + ox else ax` — the reference `automatonStep`'s
    /// `.automaton`, discharged AT THE GATE. That is what lets
    /// `AutomataflTurnCapstone.astep_newAuto_pi_of_sat` be stated against the full
    /// `automatonStepCfg` semantics rather than against the column expression `ax + ox`.
    #[test]
    fn the_new_auto_pin_is_the_degree_2_mask_form() {
        use dregg_circuit::descriptor_ir2::eval_lean_expr;
        let desc = descriptor_by_name(&step_descriptor_name(11)).unwrap();
        let binds = pi_binding_cols(&desc);
        // The published coordinate columns, read off the descriptor's own PI bindings.
        let auto_in = step_auto_in_pi(11);
        let auto_out = step_auto_out_pi(11, &desc).expect("the descriptor publishes NAX/NAY");

        for k in 0..2 {
            let ncol = binds[&(auto_out + k)];
            let acol = binds[&(auto_in + k)];
            let gates = gates_touching(&desc, ncol);
            assert_eq!(
                gates.len(),
                1,
                "exactly ONE gate pins the published coordinate column {ncol}"
            );
            let gate = gates[0];
            let mut vars = Vec::new();
            collect_expr_vars(gate, &mut vars);
            assert_eq!(
                vars.len(),
                4,
                "the pin references NAX, AX, M and OX — the degree-1 pin referenced only 3"
            );
            assert!(
                vars.contains(&acol),
                "and one of them is the CONSUMED coordinate"
            );
            let others: Vec<usize> = vars
                .iter()
                .copied()
                .filter(|c| *c != ncol && *c != acol)
                .collect();

            // Which extra column is the MASK and which the OFFSET is read from BEHAVIOUR, not
            // from a hardcoded index: exactly one orientation can act as `NAX = AX + M·OX`.
            let mut ok = false;
            for &(mcol, ocol) in &[(others[0], others[1]), (others[1], others[0])] {
                let mut row = vec![BabyBear::ZERO; desc.trace_width];
                row[acol] = BabyBear::from_u64(4);
                row[ocol] = BabyBear::from_u64(3);
                // BLOCKED (m = 0, nonzero offset): only `NAX = AX` satisfies the gate.
                row[mcol] = BabyBear::ZERO;
                row[ncol] = BabyBear::from_u64(4);
                let blocked_old = eval_lean_expr(gate, &row) == BabyBear::ZERO;
                row[ncol] = BabyBear::from_u64(7); // the retired degree-1 value `ax + ox`
                let blocked_moved = eval_lean_expr(gate, &row) == BabyBear::ZERO;
                // MOVED (m = 1): only `NAX = AX + OX` satisfies it.
                row[mcol] = BabyBear::ONE;
                let moved_moved = eval_lean_expr(gate, &row) == BabyBear::ZERO;
                row[ncol] = BabyBear::from_u64(4);
                let moved_old = eval_lean_expr(gate, &row) == BabyBear::ZERO;
                if blocked_old && !blocked_moved && moved_moved && !moved_old {
                    ok = true;
                    break;
                }
            }
            assert!(
                ok,
                "column {ncol}'s pin does not behave as `NAX = AX + M·OX` — the emitted gate is \
                 NOT the degree-2 mask form (a degree-1 `NAX = AX + OX` pin fails here: it would \
                 force the MOVED coordinate on the m = 0 branch)"
            );
        }
    }

    /// **WHY THE MASK IS THE RIGHT PIN, STATED HONESTLY.** The blocked branch (`m = 0` with a
    /// NONZERO sensed offset) is a real branch of the AIR's case split and of the Lean capstone's
    /// `.automaton = if m = 1 then (ax+ox, ay+oy) else (ax, ay)` — but it is **not reachable under
    /// the reference dynamics**: every arm of `evaluate_axis` that yields a nonzero offset carries
    /// a `dist > 1` guard (or picks the farther of two repulsors), so the first cell in the chosen
    /// direction is always in-bounds and vacuum, and the guard fires.
    ///
    /// This test pins that, exhaustively over the sensing configurations that decide it: for a set
    /// of automaton positions, every choice of `{nothing, REP@d, ATT@d}` in each of the four
    /// directions. Off-ray cells cannot change either the sensing or the target's occupancy, so
    /// this covers the question.
    ///
    /// The consequence, said plainly: the retired degree-1 pin was not rejecting reachable honest
    /// trajectories. Its defect was in the GUARANTEE — the strongest transport statable over it was
    /// the column-level `PI = ax + ox`, and lifting that to `PI = (automatonStepCfg …).automaton`
    /// would have required exactly the reachability argument this test only samples. The mask pin
    /// discharges the case split at the gate, so the transport is unconditional.
    #[test]
    fn a_nonzero_sensed_offset_always_targets_an_in_bounds_vacuum_cell() {
        use crate::reference::automaton_sense;
        let n = 11usize;
        let dirs: [(i32, i32); 4] = [(1, 0), (-1, 0), (0, 1), (0, -1)];
        let mut checked = 0usize;
        for &(ax, ay) in &[
            (5i32, 5i32),
            (0, 0),
            (10, 10),
            (0, 5),
            (5, 0),
            (10, 5),
            (5, 10),
            (1, 1),
            (9, 9),
            (2, 7),
        ] {
            // Per direction: how far a piece could be placed before leaving the board.
            let room: Vec<i32> = dirs
                .iter()
                .map(|d| {
                    let mut r = 0;
                    while (0..n as i32).contains(&(ax + d.0 * (r + 1)))
                        && (0..n as i32).contains(&(ay + d.1 * (r + 1)))
                    {
                        r += 1;
                    }
                    r
                })
                .collect();
            // option 0 = nothing; then (kind, dist) for kind ∈ {REP, ATT}, dist ∈ 1..=room.
            let opts: Vec<Vec<Option<(u8, i32)>>> = room
                .iter()
                .map(|&r| {
                    let mut v = vec![None];
                    for kind in [REP, ATT] {
                        for d in 1..=r {
                            v.push(Some((kind, d)));
                        }
                    }
                    v
                })
                .collect();
            for o0 in &opts[0] {
                for o1 in &opts[1] {
                    for o2 in &opts[2] {
                        for o3 in &opts[3] {
                            let mut cells = vec![VAC; n * n];
                            cells[(ay as usize) * n + ax as usize] = AUTO;
                            for (d, o) in dirs.iter().zip([o0, o1, o2, o3]) {
                                if let Some((kind, dist)) = o {
                                    let (px, py) = (ax + d.0 * dist, ay + d.1 * dist);
                                    cells[(py as usize) * n + px as usize] = *kind;
                                }
                            }
                            let b = Board {
                                n,
                                cells,
                                auto: (ax, ay),
                                col_rule: true,
                            };
                            let off = automaton_sense(&b).offset;
                            checked += 1;
                            if off == (0, 0) {
                                continue;
                            }
                            let target = (ax + off.0, ay + off.1);
                            assert!(
                                b.in_bounds(target) && b.cell_at(target) == VAC,
                                "auto at ({ax},{ay}) senses offset {off:?} onto a BLOCKED target \
                                 {target:?} — the blocked branch IS reachable after all, and the \
                                 degree-1 `ax + ox` pin would have refused this honest position"
                            );
                            assert_eq!(
                                automaton_step(&b).auto,
                                target,
                                "…and the reference takes it"
                            );
                        }
                    }
                }
            }
        }
        assert!(
            checked > 10_000,
            "the sweep must actually enumerate ({checked})"
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
