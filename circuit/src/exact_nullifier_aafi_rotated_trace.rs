//! Honest rotated-state extension for the exact-nullifier AAFI trace.
//!
//! The exact AAFI core proves the nullifier-set transition and exposes its faithful FNS3
//! before/after digests.  This module welds those digests into the real 179-felt rotated state
//! payload, derives the AFTER payload by changing only the eight nullifier lanes, and materializes
//! both chip-faithful 60-carrier wide commitments.  The resulting 3,760-column rows cover the
//! entire rotated extension and public inputs 60..75 of the staged Lean descriptor.
//!
//! This remains additive to the inherited FNSP-v2 witness: [`ExactAafiTraceWitness`] intentionally
//! leaves that hidden-note band unmaterialized, so this module does not claim complete descriptor
//! satisfiability, descriptor registration, a verification key, or a live proof.

use crate::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, CHIP_WIDE_ARITY, chip_absorb_all_lanes,
};
use crate::exact_nullifier_aafi_trace::{
    EXACT_AAFI_TRACE_ROWS, ExactAafiTraceWitness, POST_STATE_COMMIT_DIGEST_COLS,
    PRE_STATE_COMMIT_DIGEST_COLS, V3_TRACE_WIDTH,
};
use crate::field::BabyBear;
use crate::poseidon2::wire_commit_8_chip;
use std::error::Error;
use std::fmt;

pub const ROTATED_PAYLOAD_WIDTH: usize = 179;
pub const ROTATED_PRE_LIMBS: usize = 178;
pub const ROTATED_IROOT_OFFSET: usize = 178;
pub const BEFORE_PAYLOAD_BASE: usize = V3_TRACE_WIDTH;
pub const AFTER_PAYLOAD_BASE: usize = BEFORE_PAYLOAD_BASE + ROTATED_PAYLOAD_WIDTH;
pub const ROTATED_HOST_WIDTH: usize = AFTER_PAYLOAD_BASE + ROTATED_PAYLOAD_WIDTH;

pub const WIDE_CARRIERS: usize = 60;
pub const WIDE_CARRIER_WIDTH: usize = CHIP_OUT_LANES;
pub const WIDE_BLOCK_WIDTH: usize = WIDE_CARRIERS * WIDE_CARRIER_WIDTH;
pub const BEFORE_CARRIER_BASE: usize = ROTATED_HOST_WIDTH;
pub const AFTER_CARRIER_BASE: usize = BEFORE_CARRIER_BASE + WIDE_BLOCK_WIDTH;
pub const ROTATED_TRACE_WIDTH: usize = AFTER_CARRIER_BASE + WIDE_BLOCK_WIDTH;
pub const WIDE_COMMIT_CARRIER: usize = WIDE_CARRIERS - 1;
pub const BEFORE_COMMIT_BASE: usize =
    BEFORE_CARRIER_BASE + WIDE_COMMIT_CARRIER * WIDE_CARRIER_WIDTH;
pub const AFTER_COMMIT_BASE: usize = AFTER_CARRIER_BASE + WIDE_COMMIT_CARRIER * WIDE_CARRIER_WIDTH;

pub const OUTER_PUBLIC_INPUT_BASE: usize = 60;
pub const OUTER_PUBLIC_INPUTS: usize = 2 * CHIP_OUT_LANES;
pub const ROTATED_PUBLIC_INPUT_COUNT: usize = OUTER_PUBLIC_INPUT_BASE + OUTER_PUBLIC_INPUTS;

/// The non-contiguous nullifier octet inside the 179-felt rotated payload.
pub const NULLIFIER_OFFSETS: [usize; CHIP_OUT_LANES] = [26, 68, 69, 70, 71, 72, 73, 74];
pub const STABLE_FRAME_CELLS: usize = ROTATED_PAYLOAD_WIDTH - NULLIFIER_OFFSETS.len();
pub const WIDE_EVENTS_PER_ROW: usize = 2 * WIDE_CARRIERS;
pub const WIDE_EVENTS: usize = EXACT_AAFI_TRACE_ROWS * WIDE_EVENTS_PER_ROW;

const _: () = {
    assert!(V3_TRACE_WIDTH == 2442);
    assert!(BEFORE_PAYLOAD_BASE == 2442);
    assert!(AFTER_PAYLOAD_BASE == 2621);
    assert!(ROTATED_HOST_WIDTH == 2800);
    assert!(BEFORE_CARRIER_BASE == 2800);
    assert!(AFTER_CARRIER_BASE == 3280);
    assert!(BEFORE_COMMIT_BASE == 3272);
    assert!(AFTER_COMMIT_BASE == 3752);
    assert!(ROTATED_TRACE_WIDTH == 3760);
    assert!(ROTATED_PUBLIC_INPUT_COUNT == 76);
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RotatedStateSide {
    Before,
    After,
}

/// One table-1 lookup in a chip-faithful rotated-state commitment chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactAafiWideEvent {
    pub main_row: usize,
    pub side: RotatedStateSide,
    pub carrier: usize,
    pub output_base: usize,
    pub arity: usize,
    /// The descriptor's complete 16-lane padded input segment.
    pub inputs: [BabyBear; CHIP_RATE],
    pub output: [BabyBear; CHIP_OUT_LANES],
}

impl ExactAafiWideEvent {
    pub fn lookup_tuple(self) -> [BabyBear; CHIP_TUPLE_LEN] {
        let mut tuple = [BabyBear::ZERO; CHIP_TUPLE_LEN];
        tuple[0] = BabyBear::new(self.arity as u32);
        tuple[1..1 + CHIP_RATE].copy_from_slice(&self.inputs);
        tuple[1 + CHIP_RATE..].copy_from_slice(&self.output);
        tuple
    }

    pub fn is_genuine(self) -> bool {
        chip_absorb_all_lanes(self.arity, &self.inputs) == self.output
    }
}

/// The exact core rows extended through the rotated-state/wide-commitment boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactAafiRotatedTraceWitness {
    rows: Vec<Vec<BabyBear>>,
    before_payload: [BabyBear; ROTATED_PAYLOAD_WIDTH],
    after_payload: [BabyBear; ROTATED_PAYLOAD_WIDTH],
    wide_events: Vec<ExactAafiWideEvent>,
    outer_public_inputs: [BabyBear; OUTER_PUBLIC_INPUTS],
}

impl ExactAafiRotatedTraceWitness {
    pub fn rows(&self) -> &[Vec<BabyBear>] {
        &self.rows
    }

    pub fn before_payload(&self) -> &[BabyBear; ROTATED_PAYLOAD_WIDTH] {
        &self.before_payload
    }

    pub fn after_payload(&self) -> &[BabyBear; ROTATED_PAYLOAD_WIDTH] {
        &self.after_payload
    }

    pub fn wide_events(&self) -> &[ExactAafiWideEvent] {
        &self.wide_events
    }

    /// Public-input suffix 60..75: BEFORE carrier 59 on row zero, then AFTER carrier 59 on row 15.
    pub fn outer_public_inputs(&self) -> &[BabyBear; OUTER_PUBLIC_INPUTS] {
        &self.outer_public_inputs
    }

    pub fn before_commit(&self) -> [BabyBear; CHIP_OUT_LANES] {
        self.outer_public_inputs[..CHIP_OUT_LANES]
            .try_into()
            .expect("fixed-width before commitment")
    }

    pub fn after_commit(&self) -> [BabyBear; CHIP_OUT_LANES] {
        self.outer_public_inputs[CHIP_OUT_LANES..]
            .try_into()
            .expect("fixed-width after commitment")
    }

    pub fn all_wide_events_are_genuine(&self) -> bool {
        self.wide_events
            .iter()
            .copied()
            .all(ExactAafiWideEvent::is_genuine)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactAafiRotatedTraceError {
    InvalidCoreGeometry,
    BeforeNullifierMismatch { lane: usize, offset: usize },
    InternalInvariant(&'static str),
}

impl fmt::Display for ExactAafiRotatedTraceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCoreGeometry => write!(
                f,
                "exact-AAFI core must contain {EXACT_AAFI_TRACE_ROWS} rows of width {V3_TRACE_WIDTH}"
            ),
            Self::BeforeNullifierMismatch { lane, offset } => write!(
                f,
                "rotated BEFORE nullifier lane {lane} at payload offset {offset} does not equal the proved pre-FNS3 digest"
            ),
            Self::InternalInvariant(which) => {
                write!(f, "rotated exact-AAFI trace invariant failed: {which}")
            }
        }
    }
}

impl Error for ExactAafiRotatedTraceError {}

fn read_digest(row: &[BabyBear], cols: [usize; CHIP_OUT_LANES]) -> [BabyBear; CHIP_OUT_LANES] {
    cols.map(|col| row[col])
}

fn write_payload(row: &mut [BabyBear], base: usize, payload: &[BabyBear; ROTATED_PAYLOAD_WIDTH]) {
    row[base..base + ROTATED_PAYLOAD_WIDTH].copy_from_slice(payload);
}

fn fill_wide_chain(
    row: &mut [BabyBear],
    main_row: usize,
    side: RotatedStateSide,
    payload: &[BabyBear; ROTATED_PAYLOAD_WIDTH],
    carrier_base: usize,
    events: &mut Vec<ExactAafiWideEvent>,
) -> Result<[BabyBear; CHIP_OUT_LANES], ExactAafiRotatedTraceError> {
    let event_start = events.len();
    let mut inputs = [BabyBear::ZERO; CHIP_RATE];
    inputs[..4].copy_from_slice(&payload[..4]);
    let mut output = chip_absorb_all_lanes(4, &inputs);
    row[carrier_base..carrier_base + CHIP_OUT_LANES].copy_from_slice(&output);
    events.push(ExactAafiWideEvent {
        main_row,
        side,
        carrier: 0,
        output_base: carrier_base,
        arity: 4,
        inputs,
        output,
    });

    let mut carrier = 1usize;
    let mut limb = 4usize;
    while limb < ROTATED_PRE_LIMBS {
        inputs = [BabyBear::ZERO; CHIP_RATE];
        inputs[..CHIP_OUT_LANES].copy_from_slice(&output);
        let remaining = ROTATED_PRE_LIMBS - limb;
        let arity = if remaining >= 3 {
            inputs[8..11].copy_from_slice(&payload[limb..limb + 3]);
            limb += 3;
            CHIP_WIDE_ARITY
        } else {
            inputs[8] = payload[limb];
            limb += 1;
            9
        };
        output = chip_absorb_all_lanes(arity, &inputs);
        let output_base = carrier_base + carrier * CHIP_OUT_LANES;
        row[output_base..output_base + CHIP_OUT_LANES].copy_from_slice(&output);
        events.push(ExactAafiWideEvent {
            main_row,
            side,
            carrier,
            output_base,
            arity,
            inputs,
            output,
        });
        carrier += 1;
    }

    inputs = [BabyBear::ZERO; CHIP_RATE];
    inputs[..CHIP_OUT_LANES].copy_from_slice(&output);
    inputs[8] = payload[ROTATED_IROOT_OFFSET];
    output = chip_absorb_all_lanes(CHIP_WIDE_ARITY, &inputs);
    let output_base = carrier_base + carrier * CHIP_OUT_LANES;
    row[output_base..output_base + CHIP_OUT_LANES].copy_from_slice(&output);
    events.push(ExactAafiWideEvent {
        main_row,
        side,
        carrier,
        output_base,
        arity: CHIP_WIDE_ARITY,
        inputs,
        output,
    });

    if carrier != WIDE_COMMIT_CARRIER || events.len() - event_start != WIDE_CARRIERS {
        return Err(ExactAafiRotatedTraceError::InternalInvariant(
            "wide carrier count",
        ));
    }
    if output != wire_commit_8_chip(&payload[..ROTATED_PRE_LIMBS], payload[ROTATED_IROOT_OFFSET]) {
        return Err(ExactAafiRotatedTraceError::InternalInvariant(
            "wide commitment primitive differential",
        ));
    }
    Ok(output)
}

/// Extend a hostile-input-validated exact-AAFI trace through the rotated state boundary.
///
/// The supplied payload's eight nullifier cells must equal the core's proved pre-FNS3 digest;
/// mismatches fail before any construction. AFTER is derived from the validated BEFORE payload by
/// replacing only those eight cells with the proved post-FNS3 digest.
pub fn marshal_exact_aafi_rotated_trace(
    core: &ExactAafiTraceWitness,
    before_payload: [BabyBear; ROTATED_PAYLOAD_WIDTH],
) -> Result<ExactAafiRotatedTraceWitness, ExactAafiRotatedTraceError> {
    if core.rows().len() != EXACT_AAFI_TRACE_ROWS
        || core.rows().iter().any(|row| row.len() != V3_TRACE_WIDTH)
    {
        return Err(ExactAafiRotatedTraceError::InvalidCoreGeometry);
    }

    let core_last = &core.rows()[EXACT_AAFI_TRACE_ROWS - 1];
    let pre_fns3 = read_digest(core_last, PRE_STATE_COMMIT_DIGEST_COLS);
    let post_fns3 = read_digest(core_last, POST_STATE_COMMIT_DIGEST_COLS);
    for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
        if before_payload[offset] != pre_fns3[lane] {
            return Err(ExactAafiRotatedTraceError::BeforeNullifierMismatch { lane, offset });
        }
    }
    let mut after_payload = before_payload;
    for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
        after_payload[offset] = post_fns3[lane];
    }

    let mut rows = Vec::with_capacity(EXACT_AAFI_TRACE_ROWS);
    let mut wide_events = Vec::with_capacity(WIDE_EVENTS);
    for (main_row, core_row) in core.rows().iter().enumerate() {
        let mut row = core_row.clone();
        row.resize(ROTATED_TRACE_WIDTH, BabyBear::ZERO);
        write_payload(&mut row, BEFORE_PAYLOAD_BASE, &before_payload);
        write_payload(&mut row, AFTER_PAYLOAD_BASE, &after_payload);
        fill_wide_chain(
            &mut row,
            main_row,
            RotatedStateSide::Before,
            &before_payload,
            BEFORE_CARRIER_BASE,
            &mut wide_events,
        )?;
        fill_wide_chain(
            &mut row,
            main_row,
            RotatedStateSide::After,
            &after_payload,
            AFTER_CARRIER_BASE,
            &mut wide_events,
        )?;
        rows.push(row);
    }
    if wide_events.len() != WIDE_EVENTS {
        return Err(ExactAafiRotatedTraceError::InternalInvariant(
            "total wide event count",
        ));
    }

    let mut outer_public_inputs = [BabyBear::ZERO; OUTER_PUBLIC_INPUTS];
    outer_public_inputs[..CHIP_OUT_LANES]
        .copy_from_slice(&rows[0][BEFORE_COMMIT_BASE..BEFORE_COMMIT_BASE + CHIP_OUT_LANES]);
    outer_public_inputs[CHIP_OUT_LANES..].copy_from_slice(
        &rows[EXACT_AAFI_TRACE_ROWS - 1][AFTER_COMMIT_BASE..AFTER_COMMIT_BASE + CHIP_OUT_LANES],
    );
    Ok(ExactAafiRotatedTraceWitness {
        rows,
        before_payload,
        after_payload,
        wide_events,
        outer_public_inputs,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::{
        TID_P2, VmConstraint2, WindowExpr, eval_lean_expr, parse_vm_descriptor2,
    };
    use crate::exact_nullifier_aafi::ExactNullifierAafi;
    use crate::exact_nullifier_aafi_trace::marshal_exact_aafi_trace;
    use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

    const STAGED: &str = include_str!(
        "../staged-descriptors/fnsp-v3/faithful-note-spend-exact-aafi-fns3-rotated-wide-state.json"
    );

    fn sample_trace() -> ExactAafiRotatedTraceWitness {
        let state = ExactNullifierAafi::new();
        let mut raw = [0u8; 32];
        raw[..2].copy_from_slice(&256u16.to_le_bytes());
        let witness = state.prepare_insert(raw, 0x1234).unwrap();
        let core = marshal_exact_aafi_trace(&witness).unwrap();
        let mut before = core::array::from_fn(|i| BabyBear::new((37 * i + 11) as u32));
        let pre = read_digest(
            &core.rows()[EXACT_AAFI_TRACE_ROWS - 1],
            PRE_STATE_COMMIT_DIGEST_COLS,
        );
        for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
            before[offset] = pre[lane];
        }
        marshal_exact_aafi_rotated_trace(&core, before).unwrap()
    }

    fn max_lean_var(expr: &LeanExpr) -> Option<usize> {
        match expr {
            LeanExpr::Var(col) => Some(*col),
            LeanExpr::Const(_) => None,
            LeanExpr::Add(left, right) | LeanExpr::Mul(left, right) => {
                match (max_lean_var(left), max_lean_var(right)) {
                    (Some(left), Some(right)) => Some(left.max(right)),
                    (some @ Some(_), None) | (None, some @ Some(_)) => some,
                    (None, None) => None,
                }
            }
        }
    }

    fn max_window_var(expr: &WindowExpr) -> Option<usize> {
        match expr {
            WindowExpr::Loc(col) | WindowExpr::Nxt(col) => Some(*col),
            WindowExpr::Const(_) => None,
            WindowExpr::Add(left, right) | WindowExpr::Mul(left, right) => {
                match (max_window_var(left), max_window_var(right)) {
                    (Some(left), Some(right)) => Some(left.max(right)),
                    (some @ Some(_), None) | (None, some @ Some(_)) => some,
                    (None, None) => None,
                }
            }
        }
    }

    fn felt_i64(value: i64) -> BabyBear {
        if value >= 0 {
            BabyBear::new(value as u32)
        } else {
            BabyBear::ZERO - BabyBear::new(value.unsigned_abs() as u32)
        }
    }

    fn eval_window(expr: &WindowExpr, local: &[BabyBear], next: &[BabyBear]) -> BabyBear {
        match expr {
            WindowExpr::Loc(col) => local[*col],
            WindowExpr::Nxt(col) => next[*col],
            WindowExpr::Const(value) => felt_i64(*value),
            WindowExpr::Add(left, right) => {
                eval_window(left, local, next) + eval_window(right, local, next)
            }
            WindowExpr::Mul(left, right) => {
                eval_window(left, local, next) * eval_window(right, local, next)
            }
        }
    }

    #[test]
    fn exact_rotated_geometry_and_derived_frame_are_pinned() {
        assert_eq!(NULLIFIER_OFFSETS, [26, 68, 69, 70, 71, 72, 73, 74]);
        assert_eq!(STABLE_FRAME_CELLS, 171);
        assert_eq!(WIDE_CARRIERS, 60);
        let trace = sample_trace();
        assert_eq!(trace.rows().len(), EXACT_AAFI_TRACE_ROWS);
        assert!(
            trace
                .rows()
                .iter()
                .all(|row| row.len() == ROTATED_TRACE_WIDTH)
        );
        assert_eq!(trace.wide_events().len(), WIDE_EVENTS);
        assert!(trace.all_wide_events_are_genuine());

        let last = &trace.rows()[EXACT_AAFI_TRACE_ROWS - 1];
        let pre = read_digest(last, PRE_STATE_COMMIT_DIGEST_COLS);
        let post = read_digest(last, POST_STATE_COMMIT_DIGEST_COLS);
        let mut stable = 0usize;
        for offset in 0..ROTATED_PAYLOAD_WIDTH {
            if let Some(lane) = NULLIFIER_OFFSETS
                .iter()
                .position(|candidate| *candidate == offset)
            {
                assert_eq!(trace.before_payload()[offset], pre[lane]);
                assert_eq!(trace.after_payload()[offset], post[lane]);
            } else {
                assert_eq!(
                    trace.before_payload()[offset],
                    trace.after_payload()[offset]
                );
                stable += 1;
            }
        }
        assert_eq!(stable, STABLE_FRAME_CELLS);
        assert_eq!(
            trace.before_commit(),
            wire_commit_8_chip(
                &trace.before_payload()[..ROTATED_PRE_LIMBS],
                trace.before_payload()[ROTATED_IROOT_OFFSET]
            )
        );
        assert_eq!(
            trace.after_commit(),
            wire_commit_8_chip(
                &trace.after_payload()[..ROTATED_PRE_LIMBS],
                trace.after_payload()[ROTATED_IROOT_OFFSET]
            )
        );
    }

    #[test]
    fn mismatched_before_nullifier_refuses_before_construction() {
        let state = ExactNullifierAafi::new();
        let mut raw = [0u8; 32];
        raw[..2].copy_from_slice(&7u16.to_le_bytes());
        let witness = state.prepare_insert(raw, 7).unwrap();
        let core = marshal_exact_aafi_trace(&witness).unwrap();
        let pre = read_digest(
            &core.rows()[EXACT_AAFI_TRACE_ROWS - 1],
            PRE_STATE_COMMIT_DIGEST_COLS,
        );
        let mut before = [BabyBear::ZERO; ROTATED_PAYLOAD_WIDTH];
        for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
            before[offset] = pre[lane];
        }
        before[NULLIFIER_OFFSETS[0]] += BabyBear::ONE;
        assert!(matches!(
            marshal_exact_aafi_rotated_trace(&core, before),
            Err(ExactAafiRotatedTraceError::BeforeNullifierMismatch {
                lane: 0,
                offset: 26
            })
        ));
    }

    #[test]
    fn emitted_rotated_constraints_and_all_wide_tuples_accept_the_extension() {
        let descriptor = parse_vm_descriptor2(STAGED).expect("staged Lean descriptor parses");
        assert_eq!(descriptor.trace_width, ROTATED_TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, ROTATED_PUBLIC_INPUT_COUNT);
        assert_eq!(descriptor.constraints.len(), 1258);
        let trace = sample_trace();

        let wide: Vec<_> = descriptor
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::Lookup(lookup) if lookup.table == TID_P2 => Some(lookup),
                _ => None,
            })
            .collect();
        assert_eq!(wide.len(), WIDE_EVENTS_PER_ROW);
        for (main_row, row) in trace.rows().iter().enumerate() {
            let events = &trace.wide_events()
                [main_row * WIDE_EVENTS_PER_ROW..(main_row + 1) * WIDE_EVENTS_PER_ROW];
            for (site, (lookup, event)) in wide.iter().zip(events).enumerate() {
                let emitted: Vec<_> = lookup
                    .tuple
                    .iter()
                    .map(|expression| eval_lean_expr(expression, row))
                    .collect();
                assert_eq!(emitted.len(), CHIP_TUPLE_LEN);
                assert_eq!(
                    emitted.as_slice(),
                    event.lookup_tuple().as_slice(),
                    "emitted wide tuple mismatch at row {main_row}, site {site}"
                );
                // The current tuple is 25-wide; output starts at 1 + CHIP_RATE = 17.
                assert_eq!(
                    &emitted[1 + CHIP_RATE..],
                    chip_absorb_all_lanes(event.arity, &event.inputs).as_slice()
                );
            }
        }

        // Evaluate the actual emitted 179 BEFORE-continuity window expressions.
        let outer_windows: Vec<_> = descriptor
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::WindowGate(gate)
                    if max_window_var(&gate.body).is_some_and(|col| col >= BEFORE_PAYLOAD_BASE) =>
                {
                    Some(gate)
                }
                _ => None,
            })
            .collect();
        assert_eq!(outer_windows.len(), ROTATED_PAYLOAD_WIDTH);
        assert!(outer_windows.iter().all(|gate| gate.on_transition));
        for pair in trace.rows().windows(2) {
            for gate in &outer_windows {
                assert_eq!(eval_window(&gate.body, &pair[0], &pair[1]), BabyBear::ZERO);
            }
        }

        // Exactly 171 stable-frame + 16 FNS3 weld expressions mention the appended payload.
        let outer_boundaries: Vec<_> = descriptor
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: VmRow::Last,
                    body,
                }) if max_lean_var(body).is_some_and(|col| col >= BEFORE_PAYLOAD_BASE) => {
                    Some(body)
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            outer_boundaries.len(),
            STABLE_FRAME_CELLS + 2 * CHIP_OUT_LANES
        );
        let last = &trace.rows()[EXACT_AAFI_TRACE_ROWS - 1];
        for body in outer_boundaries {
            assert_eq!(eval_lean_expr(body, last), BabyBear::ZERO);
        }

        let outer_pins: Vec<_> = descriptor
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                    if *pi_index >= OUTER_PUBLIC_INPUT_BASE =>
                {
                    Some((*row, *col, *pi_index))
                }
                _ => None,
            })
            .collect();
        assert_eq!(outer_pins.len(), OUTER_PUBLIC_INPUTS);
        for (row_tag, col, pi_index) in outer_pins {
            let row = match row_tag {
                VmRow::First => &trace.rows()[0],
                VmRow::Last => &trace.rows()[EXACT_AAFI_TRACE_ROWS - 1],
            };
            assert_eq!(
                row[col],
                trace.outer_public_inputs()[pi_index - OUTER_PUBLIC_INPUT_BASE]
            );
        }
    }
}
