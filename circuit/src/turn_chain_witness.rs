//! Witness builder for the Lean-emitted whole-history turn-chain descriptor.
//!
//! The constraints are authored and proved in
//! `metatheory/Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean`; this module only builds
//! the main-trace witness consumed by `prove_vm_descriptor2`. One row carries the seven scalar
//! columns
//!
//! `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]`
//!
//! and NOTHING else: E7 narrowed the descriptor's chip lookup onto the NARROW bus
//! (`chipLookupTupleNarrow`, wire `TID_P2_NARROW`), so out0 (`ACC_OUT`) alone serves it and the
//! seven nonzero-index Poseidon2 output lanes no longer ride the main trace. Real rows are
//! padded to a power of two with `(old_root, new_root) = (final_root, final_root)`, a continuing
//! positional index, a frozen real-row count, and a genuinely continued hash chain. This is the
//! production padding contract that makes the emitted `on_transition := true` continuity and index
//! gates sound across real-to-padding and padding-to-padding boundaries.

use crate::descriptor_ir2::chip_absorb_all_lanes;
use crate::field::BabyBear;

/// Dispatch name of the Lean-emitted descriptor.
pub const TURN_CHAIN_BINDING_NAME: &str = "dregg-turn-chain-binding-v2";

/// Main-trace column layout, identical to `EffectVmEmitTurnChainBinding.Chain`.
pub const OLD_ROOT: usize = 0;
pub const NEW_ROOT: usize = 1;
pub const ACC_IN: usize = 2;
pub const ACC_OUT: usize = 3;
pub const IDX: usize = 4;
pub const IS_REAL: usize = 5;
pub const REAL_COUNT: usize = 6;
/// Total main-trace width: the 7 scalar columns. E7 deleted the trailing 7-lane block `[7, 14)` —
/// a pure tail truncation, so no scalar column moved.
pub const TURN_CHAIN_BINDING_WIDTH: usize = REAL_COUNT + 1; // 7

/// Public-input layout `[genesis_root, final_root, num_turns, chain_digest]`.
pub const PI_GENESIS_ROOT: usize = 0;
pub const PI_FINAL_ROOT: usize = 1;
pub const PI_NUM_TURNS: usize = 2;
pub const PI_CHAIN_DIGEST: usize = 3;
pub const TURN_CHAIN_BINDING_PI_COUNT: usize = 4;

/// Build one chip-lane-layout row and return `(acc_out, row)`.
fn binding_row(
    old_root: BabyBear,
    new_root: BabyBear,
    acc_in: BabyBear,
    idx: BabyBear,
    is_real: bool,
    real_count: BabyBear,
) -> (BabyBear, Vec<BabyBear>) {
    // The arity-4 chip row is exactly the emitted lookup preimage
    // `[acc_in, old_root, new_root, idx]`. Lane 0 is ACC_OUT; on the NARROW bus that is the whole
    // of the tuple's output, so lanes 1..7 are computed and discarded.
    let acc_out = chip_absorb_all_lanes(4, &[acc_in, old_root, new_root, idx])[0];
    let mut row = vec![BabyBear::ZERO; TURN_CHAIN_BINDING_WIDTH];
    row[OLD_ROOT] = old_root;
    row[NEW_ROOT] = new_root;
    row[ACC_IN] = acc_in;
    row[ACC_OUT] = acc_out;
    row[IDX] = idx;
    row[IS_REAL] = if is_real {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    row[REAL_COUNT] = real_count;
    (acc_out, row)
}

/// Build the chip-lane-layout trace and four public inputs for an ordered sequence of scalar
/// `(old_root, new_root)` turn endpoints.
///
/// At least two turns are required. The input sequence must already be continuous: every pair's
/// `old_root` must equal its predecessor's `new_root`. The returned trace height is
/// `turns.len().next_power_of_two().max(2)`. Padding rows carry the final root on both endpoint
/// columns, continue `idx`, freeze `real_count`, set `is_real = 0`, and continue the genuine
/// Poseidon2 accumulator.
///
/// This function computes witness values only. The Lean-emitted descriptor remains the sole judge
/// of continuity, indexing, real-row counting, public bindings, and hash correctness.
pub fn turn_chain_binding_witness(
    turns: &[(BabyBear, BabyBear)],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if turns.len() < 2 {
        return Err(format!(
            "turn-chain binding needs at least 2 turns, got {}",
            turns.len()
        ));
    }
    for i in 1..turns.len() {
        if turns[i - 1].1 != turns[i].0 {
            return Err(format!(
                "turn {i} breaks continuity: old_root {} != previous new_root {}",
                turns[i].0.as_u32(),
                turns[i - 1].1.as_u32()
            ));
        }
    }

    let n = turns.len();
    let padded_len = n.next_power_of_two().max(2);
    let mut trace = Vec::with_capacity(padded_len);
    let mut acc = BabyBear::ZERO;
    let mut real_count = BabyBear::ZERO;

    for (i, &(old_root, new_root)) in turns.iter().enumerate() {
        real_count += BabyBear::ONE;
        let (acc_out, row) = binding_row(
            old_root,
            new_root,
            acc,
            BabyBear::new(i as u32),
            true,
            real_count,
        );
        trace.push(row);
        acc = acc_out;
    }

    let final_root = turns[n - 1].1;
    for i in n..padded_len {
        let (acc_out, row) = binding_row(
            final_root,
            final_root,
            acc,
            BabyBear::new(i as u32),
            false,
            real_count,
        );
        trace.push(row);
        acc = acc_out;
    }

    let pis = vec![turns[0].0, final_root, BabyBear::new(n as u32), acc];
    debug_assert_eq!(pis.len(), TURN_CHAIN_BINDING_PI_COUNT);
    debug_assert!(
        trace
            .iter()
            .all(|row| row.len() == TURN_CHAIN_BINDING_WIDTH)
    );
    Ok((trace, pis))
}
