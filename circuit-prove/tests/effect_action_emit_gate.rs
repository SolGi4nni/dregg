//! # The emit-from-Lean EQUALITY GATE — the generalized effect-action binding AIR.
//!
//! ⚑⚑ **GREEN SINCE 2026-08-06 — and here is what was RED, because the shape of the fix is the
//! interesting part.** Six of this file's tests failed (plus one in
//! `effect_action_extra_tamper_audit.rs`), and the `challenges` flag-day repair was NOT the cause;
//! it is what made the cause visible. [`BURN_GOLDEN`] was made byte-identical to
//! `EffectActionBindingEmit.lean`'s `#guard emitVmJson2 burnDesc`, and `parse_vm_descriptor2`
//! refused it:
//!
//! ```text
//! constant at byte 3619 does not fit a BabyBear felt (10 decimal digits,
//! p_babybear = 2013265921). A gate body carrying it cannot round-trip the field, so its
//! integer semantics say nothing about any proof over it.
//! ```
//!
//! The constant was `TWO_POW_32 = 4294967296`, the borrow coefficient of the two-limb u64
//! subtraction. BabyBear's `p` is `2013265921 < 2^32`, so it had no felt. **That PREDATED the flag
//! day** — the retired inline golden carried the identical constant and simply failed one check
//! earlier, on the missing `"challenges"` key, so the deeper refusal was never reached.
//!
//! ⚠ **The remedy was NOT `parse_vm_descriptor2_unsound_oversized`.** That escape exists to read an
//! artifact, not to make a gate green over an encoding whose integer semantics do not survive the
//! field. Nor was it writing `2^32 mod p`: the gate would have parsed and stopped meaning the
//! subtraction it claims. The ENCODING was wrong in BOTH directions — a 32-bit limb is not even
//! injective into a felt, because `BabyBear::new` reduces, so `lo = 0` and `lo = p` were one cell.
//!
//! The fix is in the AUTHOR: `AMOUNT_LIMBS` 2 -> 4 at 16 bits, so a u64 is exactly four limbs, the
//! borrow weight is `2^16 = 65536`, and every chain body is bounded by `2^18` — far inside `p`. The
//! top chain gate carries NO outgoing borrow, which makes `amount <= old_balance` an in-circuit
//! tooth for the first time ([`burn_underflow_refuses`]). See
//! `Dregg2.Circuit.Emit.EffectActionBindingEmit` (`burn_chain_exact_of_modEq`,
//! `chainBody_abs_lt_p`) for the field-to-ℤ bridge this width exists to make true.
//!
//! Validates the `emit-from-Lean` pattern for the `effect_action` family: the binding AIR
//! `circuit/src/effect_action_air.rs::EffectActionAir` (a 32-byte field → 8 BabyBear limbs, a u64
//! amount → 4 x 16-bit limbs, each pinned to a row-0 trace column; row-continuity forcing every row to
//! equal row 0; and — for the `Burn` schema — the two-limb u64 subtraction with a boolean borrow
//! plus the `was_burn` disclosure pin).
//!
//! The descriptors are AUTHORED in Lean
//! (`metatheory/Dregg2/Circuit/Emit/EffectActionBindingEmit.lean`, `revokeCapabilityDesc` +
//! `burnDesc`) and their wire strings are byte-pinned there (`emitVmJson2` `#guard`). This test
//! embeds those EXACT strings ([`REVOKE_GOLDEN`], [`BURN_GOLDEN`]), and:
//!
//!   1. DECODES each via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST binding witness (the SAME limb encoding the hand AIR uses,
//!      `effect_vm::bytes32_to_8_limbs` + `effect_action_air::encode_amount`) through [`prove_vm_descriptor2`], asserts
//!      ACCEPT, and re-verifies;
//!   3. the MUTATION CANARIES — each tampers exactly one thing and asserts refusal, and each bites a
//!      NAMED constraint:
//!        * a forged public-input limb → the `pi_binding` (the full-fidelity binding tooth);
//!        * a broken `new_balance = old_balance - amount` (trace AND PI moved together, so the pin
//!          still holds) → the Burn limb-0 chain `gate`;
//!        * a FORGED BORROW BIT (an aux column, so every PI pin still holds) → the two chain gates
//!          that read it — the pole the felt-sized borrow weight exists for;
//!        * an UNDERFLOWING burn (`0 - 1` wrapping to `u64::MAX`) → the TOP chain gate, which
//!          carries no outgoing borrow;
//!        * `was_burn_flag != 1` (trace AND PI together) → the Burn disclosure `gate`;
//!        * a value stashed in a later row (row 0 still pinned) → the continuity `window_gate`.
//!
//! The canaries are NON-VACUOUS by construction: each first asserts the honest witness ACCEPTS,
//! and for the arithmetic/disclosure canaries the tampered PI still matches the tampered row (so the
//! `pi_binding` is satisfied and the ONLY violated relation is the targeted `gate`).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_action_air::encode_amount;
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::refusal::{Outcome, classify};

// ── The byte-identical wire strings Lean's `emitVmJson2` emits (pinned by the `#guard`s in
//    `EffectActionBindingEmit.lean`). Drift on either side breaks the Lean `#guard` or the Rust
//    `decoded == hand_built` assertion. ──
const REVOKE_GOLDEN: &str = r#"{"name":"dregg-effect-revoke-capability-v1","ir":2,"trace_width":12,"public_input_count":12,"challenges":0,"tables":[],"constraints":[{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":0}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":3}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":6}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":7}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":8}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":9},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":9}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":10},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":10}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":11},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":11}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9},{"t":"pi_binding","row":"first","col":10,"pi_index":10},{"t":"pi_binding","row":"first","col":11,"pi_index":11}],"hash_sites":[],"ranges":[]}"#;
const BURN_GOLDEN: &str = r#"{"name":"dregg-effect-burn-v1","ir":2,"trace_width":27,"public_input_count":24,"challenges":0,"tables":[],"constraints":[{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":0}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":3}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":6}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":7}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":8}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":9},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":9}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":10},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":10}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":11},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":11}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":12},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":12}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":13}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":14},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":14}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":15},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":15}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":16}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":17},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":17}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":18},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":18}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":19},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":19}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":20},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":20}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":21},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":21}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":22},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":22}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":23},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":23}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":24},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":24}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":25},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":25}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":26},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":26}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9},{"t":"pi_binding","row":"first","col":10,"pi_index":10},{"t":"pi_binding","row":"first","col":11,"pi_index":11},{"t":"pi_binding","row":"first","col":12,"pi_index":12},{"t":"pi_binding","row":"first","col":13,"pi_index":13},{"t":"pi_binding","row":"first","col":14,"pi_index":14},{"t":"pi_binding","row":"first","col":15,"pi_index":15},{"t":"pi_binding","row":"first","col":16,"pi_index":16},{"t":"pi_binding","row":"first","col":17,"pi_index":17},{"t":"pi_binding","row":"first","col":18,"pi_index":18},{"t":"pi_binding","row":"first","col":19,"pi_index":19},{"t":"pi_binding","row":"first","col":20,"pi_index":20},{"t":"pi_binding","row":"first","col":21,"pi_index":21},{"t":"pi_binding","row":"first","col":22,"pi_index":22},{"t":"pi_binding","row":"first","col":23,"pi_index":23},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":12},"r":{"t":"var","v":16}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":24}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":13},"r":{"t":"var","v":17}},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":25}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":14},"r":{"t":"var","v":18}},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":26}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":15},"r":{"t":"var","v":19}},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":11}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}},{"t":"gate","body":{"t":"var","v":21}},{"t":"gate","body":{"t":"var","v":22}},{"t":"gate","body":{"t":"var","v":23}}],"hash_sites":[],"ranges":[]}"#;

// ── Descriptor builders (the independent "hand AIR semantics" twins). ──

/// The continuity `window_gate` for column `c`: `Nxt c - Loc c`, on the transition domain.
fn cont_gate(c: usize) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(c)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(WindowExpr::Loc(c)),
            )),
        ),
        on_transition: true,
    })
}

/// The row-0 PI pin for slot `c`.
fn pi_gate(c: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: c,
        pi_index: c,
    })
}

fn v(i: usize) -> LeanExpr {
    LeanExpr::Var(i)
}
fn k(x: i64) -> LeanExpr {
    LeanExpr::Const(x)
}

/// Column layout of the Burn schema (1 field + 4 amounts x 4 limbs + 3 borrow bits).
const OLD: usize = 8; // old_balance limbs   8..12
const NEW: usize = 12; // new_balance limbs 12..16
const AMT: usize = 16; // amount limbs      16..20
const WB: usize = 20; // was_burn limbs     20..24
const BRW: usize = 24; // borrow bits       24..27
/// The felt-sized limb base. ⚑ `2^16`, not `2^32`: `p_babybear = 2013265921 < 2^32`, so a `2^32`
/// coefficient has no felt and `parse_vm_descriptor2` REFUSES a descriptor carrying it.
const LIMB_BASE: i64 = 65536;

/// The eleven Burn algebraic gates, in chain order, over the Burn column layout.
fn burn_gates() -> Vec<VmConstraint2> {
    // chain limbs 0..2: new_i + amt_i + b_{i-1} - 2^16*b_i - old_i   (b_{-1} absent on limb 0)
    let c0 = LeanExpr::add(
        LeanExpr::add(v(NEW), v(AMT)),
        LeanExpr::add(
            LeanExpr::mul(k(-LIMB_BASE), v(BRW)),
            LeanExpr::mul(k(-1), v(OLD)),
        ),
    );
    let chain = |i: usize| {
        LeanExpr::add(
            LeanExpr::add(v(NEW + i), v(AMT + i)),
            LeanExpr::add(
                v(BRW + i - 1),
                LeanExpr::add(
                    LeanExpr::mul(k(-LIMB_BASE), v(BRW + i)),
                    LeanExpr::mul(k(-1), v(OLD + i)),
                ),
            ),
        )
    };
    // top limb: new_3 + amt_3 + b_2 - old_3 — NO outgoing borrow (the `amount <= old` tooth).
    let c3 = LeanExpr::add(
        LeanExpr::add(v(NEW + 3), v(AMT + 3)),
        LeanExpr::add(v(BRW + 2), LeanExpr::mul(k(-1), v(OLD + 3))),
    );
    let boolean = |c: usize| LeanExpr::mul(v(c), LeanExpr::add(v(c), k(-1)));
    vec![
        VmConstraint2::Base(VmConstraint::Gate(c0)),
        VmConstraint2::Base(VmConstraint::Gate(chain(1))),
        VmConstraint2::Base(VmConstraint::Gate(chain(2))),
        VmConstraint2::Base(VmConstraint::Gate(c3)),
        VmConstraint2::Base(VmConstraint::Gate(boolean(BRW))),
        VmConstraint2::Base(VmConstraint::Gate(boolean(BRW + 1))),
        VmConstraint2::Base(VmConstraint::Gate(boolean(BRW + 2))),
        VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(v(WB), k(-1)))),
        VmConstraint2::Base(VmConstraint::Gate(v(WB + 1))),
        VmConstraint2::Base(VmConstraint::Gate(v(WB + 2))),
        VmConstraint2::Base(VmConstraint::Gate(v(WB + 3))),
    ]
}

/// Independently hand-build the pure-binding revoke-capability descriptor (1 field + 1 amount).
fn hand_built_revoke() -> EffectVmDescriptor2 {
    let pi = 12;
    let mut constraints: Vec<VmConstraint2> = (0..pi).map(cont_gate).collect();
    constraints.extend((0..pi).map(pi_gate));
    EffectVmDescriptor2 {
        name: "dregg-effect-revoke-capability-v1".to_string(),
        trace_width: pi,
        public_input_count: pi,
        challenges: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// Independently hand-build the algebraic Burn descriptor (1 field + 4 amounts + borrow aux).
fn hand_built_burn() -> EffectVmDescriptor2 {
    let width = 27;
    let pi = 24;
    let mut constraints: Vec<VmConstraint2> = (0..width).map(cont_gate).collect();
    constraints.extend((0..pi).map(pi_gate));
    constraints.extend(burn_gates());
    EffectVmDescriptor2 {
        name: "dregg-effect-burn-v1".to_string(),
        trace_width: width,
        public_input_count: pi,
        challenges: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ── Witness builders (the SAME encoding the hand AIR uses). ──

/// One Burn binding row (width 27): field limbs + old/new/amount/was_burn 16-bit limbs + 3 borrows.
///
/// ⚑ The borrow chain is computed here EXACTLY as `effect_action_air::generate_trace` does — but
/// spelled out independently, so a drift in either shows up as a refused honest witness.
fn burn_row(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; 27];
    row[0..8].copy_from_slice(&bytes32_to_8_limbs(target));
    row[OLD..OLD + 4].copy_from_slice(&encode_amount(old));
    row[NEW..NEW + 4].copy_from_slice(&encode_amount(new));
    row[AMT..AMT + 4].copy_from_slice(&encode_amount(amount));
    row[WB..WB + 4].copy_from_slice(&encode_amount(was_burn));
    let mut borrow = 0u64;
    for i in 0..3 {
        let o = (old >> (i * 16)) & 0xFFFF;
        let a = ((amount >> (i * 16)) & 0xFFFF) + borrow;
        borrow = u64::from(o < a);
        row[BRW + i as usize] = BabyBear::new(borrow as u32);
    }
    row
}

/// The Burn public inputs (the 16 pinned columns = `row[0..16]`, exactly the hand AIR's
/// `EffectActionWitness::public_inputs()`).
fn burn_pis(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    burn_row(target, old, new, amount, was_burn)[0..24].to_vec()
}

/// A 4-row (power-of-two) base trace of identical rows.
fn rows4(row: Vec<BabyBear>) -> Vec<Vec<BabyBear>> {
    vec![row.clone(), row.clone(), row.clone(), row]
}

/// One revoke-capability binding row (width 12): cell_id limbs + slot limbs.
fn revoke_row(cell: &[u8; 32], slot: u64) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; 12];
    row[0..8].copy_from_slice(&bytes32_to_8_limbs(cell));
    row[8..12].copy_from_slice(&encode_amount(slot));
    row
}

fn revoke_pis(cell: &[u8; 32], slot: u64) -> Vec<BabyBear> {
    revoke_row(cell, slot)
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (proving refuses, panics, OR the proof fails to
/// verify); `false` iff it both proves AND verifies. Mirrors the production posture: the
/// consumer's `verify_vm_descriptor2` is the real check (`prove` self-verifies only in debug).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("rejects", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

// ── STEP 1 — the emitted descriptors decode and equal the hand-built twins. ──

#[test]
fn effect_action_emit_decodes_to_hand_built() {
    let dr = parse_vm_descriptor2(REVOKE_GOLDEN).expect("revoke golden decodes");
    assert_eq!(dr, hand_built_revoke(), "revoke: Lean emit ≡ hand-built");
    assert_eq!(dr.trace_width, 12);
    assert_eq!(dr.public_input_count, 12);

    let db = parse_vm_descriptor2(BURN_GOLDEN).expect("burn golden decodes");
    assert_eq!(db, hand_built_burn(), "burn: Lean emit ≡ hand-built");
    assert_eq!(db.trace_width, 27);
    assert_eq!(db.public_input_count, 24);

    // Constraint-shape pins.
    let n_win = |d: &EffectVmDescriptor2| {
        d.constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count()
    };
    let n_pin = |d: &EffectVmDescriptor2| {
        d.constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count()
    };
    let n_gate = |d: &EffectVmDescriptor2| {
        d.constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::Gate(_))))
            .count()
    };
    assert_eq!((n_win(&dr), n_pin(&dr), n_gate(&dr)), (12, 12, 0));
    assert_eq!((n_win(&db), n_pin(&db), n_gate(&db)), (27, 24, 11));

    // ⚑ THE POLE THE FLAG DAY EXISTS FOR: the descriptor PARSES. Its largest gate coefficient is
    // 2^16, so it round-trips a felt. Until 2026-08-06 the borrow rode 2^32 = 4294967296 and
    // `parse_vm_descriptor2` refused this exact string outright.
    assert!(
        !BURN_GOLDEN.contains("4294967296"),
        "a 2^32 coefficient has no BabyBear felt (p = 2013265921) — the descriptor cannot parse"
    );
    assert!(
        BURN_GOLDEN.contains("\"v\":-65536"),
        "the borrow weight must be 2^16"
    );
}

// ── STEP 2 — the honest binding witnesses prove and verify. ──

#[test]
fn honest_burn_binding_proves_and_verifies() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];
    // 1000 - 400 = 600, no underflow (borrow 0), was_burn = 1.
    let trace = rows4(burn_row(&target, 1000, 600, 400, 1));
    let pis = burn_pis(&target, 1000, 600, 400, 1);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest Burn binding must prove");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("honest Burn proof must re-verify");
}

#[test]
fn honest_revoke_binding_proves_and_verifies() {
    let desc = parse_vm_descriptor2(REVOKE_GOLDEN).expect("decode");
    let cell = [0xAAu8; 32];
    let trace = rows4(revoke_row(&cell, 42));
    let pis = revoke_pis(&cell, 42);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest revoke binding must prove");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("honest revoke proof must re-verify");
}

// ── STEP 3 — MUTATION CANARIES. ──

/// CANARY (pi_binding): honest Burn trace, but a FORGED public-input limb (the target_cell_id's
/// first limb). Row-0 col 0 no longer equals the claimed PI → the `pi_binding` is UNSAT. The
/// full-fidelity binding tooth: a proof cannot be re-attributed to a different parameter.
#[test]
fn burn_forged_pi_limb_refuses() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];
    let trace = rows4(burn_row(&target, 1000, 600, 400, 1));
    let honest_pis = burn_pis(&target, 1000, 600, 400, 1);
    assert!(
        !rejects(&desc, &trace, &honest_pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = honest_pis.clone();
    forged[0] = forged[0] + BabyBear::new(1); // forge the target_cell_id limb
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged PI limb must be REJECTED (pi_binding tooth)"
    );
}

/// CANARY (Burn subtraction gate): a trace claiming `new_balance = 601` while `old - amount = 600`,
/// with the PI moved to MATCH the trace (so every `pi_binding` still holds and the borrow bit is
/// honest). The ONLY violated relation is the low-limb subtraction `gate`
/// `new_lo + amt_lo - borrow*2^32 - old_lo == 0` (601 + 400 - 1000 = 1 ≠ 0) → UNSAT.
#[test]
fn burn_broken_subtraction_refuses() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];
    // honest baseline accepts.
    assert!(!rejects(
        &desc,
        &rows4(burn_row(&target, 1000, 600, 400, 1)),
        &burn_pis(&target, 1000, 600, 400, 1)
    ));
    // wrong new_balance, trace AND PI moved together (pi_binding satisfied).
    let bad_trace = rows4(burn_row(&target, 1000, 601, 400, 1));
    let bad_pis = burn_pis(&target, 1000, 601, 400, 1);
    assert!(
        rejects(&desc, &bad_trace, &bad_pis),
        "new_balance != old_balance - amount must be REJECTED by the subtraction gate"
    );
}

/// CANARY (Burn disclosure gate): `was_burn_flag = 2` (not 1), trace AND PI moved together so the
/// pins hold and the subtraction still balances (new = old - amount). The ONLY violated relation is
/// `was_burn_lo - 1 == 0` (2 - 1 = 1 ≠ 0) → UNSAT.
#[test]
fn burn_wrong_disclosure_flag_refuses() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];
    assert!(!rejects(
        &desc,
        &rows4(burn_row(&target, 1000, 600, 400, 1)),
        &burn_pis(&target, 1000, 600, 400, 1)
    ));
    let bad_trace = rows4(burn_row(&target, 1000, 600, 400, 2));
    let bad_pis = burn_pis(&target, 1000, 600, 400, 2);
    assert!(
        rejects(&desc, &bad_trace, &bad_pis),
        "was_burn_flag != 1 must be REJECTED by the disclosure gate"
    );
}

/// CANARY (continuity window_gate): honest row 0 (pinned to the honest PI), but a LATER row stashes
/// a different value in a bound column. Row 0 still satisfies `pi_binding`, but
/// `Nxt(c) - Loc(c) == 0` breaks on the 0→1 transition → UNSAT. The stash-resistance tooth.
#[test]
fn burn_stashed_later_row_refuses() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];
    let honest = burn_row(&target, 1000, 600, 400, 1);
    let pis = burn_pis(&target, 1000, 600, 400, 1);
    assert!(!rejects(&desc, &rows4(honest.clone()), &pis));
    // Stash a different target-limb in row 1 only (row 0 stays honest & pinned).
    let mut stashed = honest.clone();
    stashed[0] = stashed[0] + BabyBear::new(7);
    let trace = vec![honest.clone(), stashed, honest.clone(), honest];
    assert!(
        rejects(&desc, &trace, &pis),
        "a value stashed in a later row must be REJECTED by the continuity window_gate"
    );
}

/// CANARY (revoke pi_binding): honest revoke trace, forged slot-limb PI → `pi_binding` UNSAT.
#[test]
fn revoke_forged_pi_limb_refuses() {
    let desc = parse_vm_descriptor2(REVOKE_GOLDEN).expect("decode");
    let cell = [0xAAu8; 32];
    let trace = rows4(revoke_row(&cell, 42));
    let honest_pis = revoke_pis(&cell, 42);
    assert!(!rejects(&desc, &trace, &honest_pis));
    let mut forged = honest_pis.clone();
    forged[8] = forged[8] + BabyBear::new(1); // forge the slot limb 0
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged revoke PI limb must be REJECTED (pi_binding tooth)"
    );
}

/// A descriptor with the constraint at `idx` removed (for the drop-the-tooth non-vacuity proof).
fn drop_at(desc: &EffectVmDescriptor2, idx: usize) -> EffectVmDescriptor2 {
    let mut d = desc.clone();
    d.constraints.remove(idx);
    d
}

/// THE NON-VACUITY PROOF: each mutation canary bites its NAMED tooth, not an unrelated error.
/// Dropping EXACTLY the targeted constraint flips the SAME tampered witness from REJECT to ACCEPT —
/// so the rejection is attributable to that constraint alone. (Constraint order in `burnDesc`:
/// continuity 0..27, pi_binding 27..51, then chain limbs 51/52/53/54, borrow-bool 55/56/57,
/// was_burn limbs 58/59/60/61.)
#[test]
fn mutation_canaries_bite_named_teeth() {
    let target = [0x11u8; 32];
    let burn = hand_built_burn();

    // Subtraction: with chain limb 0 present, new=601 rejects; drop it (51) → ACCEPTS.
    let bad_sub_t = rows4(burn_row(&target, 1000, 601, 400, 1));
    let bad_sub_p = burn_pis(&target, 1000, 601, 400, 1);
    assert!(rejects(&burn, &bad_sub_t, &bad_sub_p));
    assert!(
        !rejects(&drop_at(&burn, 51), &bad_sub_t, &bad_sub_p),
        "dropping the limb-0 chain gate flips new=601 to ACCEPT — it is the biting tooth"
    );

    // Disclosure: was_burn=2 rejects; drop the was_burn limb-0 pin (58) → ACCEPTS.
    let bad_wb_t = rows4(burn_row(&target, 1000, 600, 400, 2));
    let bad_wb_p = burn_pis(&target, 1000, 600, 400, 2);
    assert!(rejects(&burn, &bad_wb_t, &bad_wb_p));
    assert!(
        !rejects(&drop_at(&burn, 58), &bad_wb_t, &bad_wb_p),
        "dropping the was_burn limb-0 pin flips flag=2 to ACCEPT — it is the biting tooth"
    );

    // PI binding: forged pi[0] rejects; drop the col-0 pin (27) → ACCEPTS.
    let honest_t = rows4(burn_row(&target, 1000, 600, 400, 1));
    let mut forged_p = burn_pis(&target, 1000, 600, 400, 1);
    forged_p[0] = forged_p[0] + BabyBear::new(1);
    assert!(rejects(&burn, &honest_t, &forged_p));
    assert!(
        !rejects(&drop_at(&burn, 27), &honest_t, &forged_p),
        "dropping the col-0 pi_binding flips the forged limb to ACCEPT — the pin is the biting tooth"
    );

    // Continuity: stashed row-1 col-0 rejects; drop the col-0 window_gate (0) → ACCEPTS.
    let honest = burn_row(&target, 1000, 600, 400, 1);
    let pis = burn_pis(&target, 1000, 600, 400, 1);
    let mut stashed = honest.clone();
    stashed[0] = stashed[0] + BabyBear::new(7);
    let stash_t = vec![honest.clone(), stashed, honest.clone(), honest];
    assert!(rejects(&burn, &stash_t, &pis));
    assert!(
        !rejects(&drop_at(&burn, 0), &stash_t, &pis),
        "dropping the col-0 continuity window_gate flips the stash to ACCEPT — it is the biting tooth"
    );
}

/// A descriptor with the constraints at `hi` and `lo` removed (`hi > lo`; drop the higher index
/// first so the lower one does not shift).
fn drop_two(desc: &EffectVmDescriptor2, hi: usize, lo: usize) -> EffectVmDescriptor2 {
    assert!(hi > lo);
    drop_at(&drop_at(desc, hi), lo)
}

/// ⚑ **CANARY (FORGED BORROW) — the pole the felt-sized encoding exists for.** The honest trace with
/// the TOP borrow bit `b_2` conjured from 0 to 1. The borrow columns are AUX (past `pi_count`), so
/// every `pi_binding` still holds and the published tuple is untouched — a prover forging this is
/// claiming `2^32` of balance out of a free witness cell. The two chain gates that read `b_2`
/// (limb 2, limb 3) refuse it.
///
/// This is exactly what the retired shape could not have refused meaningfully: its borrow rode a
/// `2^32` coefficient, which has no BabyBear felt, so the descriptor did not parse at all.
#[test]
fn burn_forged_borrow_refuses() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];
    let honest = burn_row(&target, 1000, 600, 400, 1);
    let pis = burn_pis(&target, 1000, 600, 400, 1);
    assert!(
        !rejects(&desc, &rows4(honest.clone()), &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    // The honest borrows are all zero (1000 - 400 borrows nowhere); forge the top one.
    assert_eq!(honest[BRW + 2], BabyBear::ZERO, "honest b_2 must be 0");
    let mut forged = honest.clone();
    forged[BRW + 2] = BabyBear::new(1);
    assert!(
        rejects(&desc, &rows4(forged.clone()), &pis),
        "a FORGED BORROW must be REJECTED by the chain"
    );
    // Attribution: the two chain gates that READ b_2 are the biting teeth. Drop exactly those
    // (limb-3 at 54, limb-2 at 53) and the same forgery is ACCEPTED.
    assert!(
        !rejects(&drop_two(&hand_built_burn(), 54, 53), &rows4(forged), &pis),
        "dropping the two chain gates that read b_2 flips the forged borrow to ACCEPT"
    );
}

/// ⚑ **CANARY (UNDERFLOW) — the availability tooth the retired shape did not have.** `old = 0`,
/// `amount = 1`, `new = u64::MAX` (the wrap): every borrow closes up the chain, but the TOP limb
/// carries no outgoing borrow, so `new_3 + amt_3 + b_2 - old_3` cannot vanish. A burn of more than
/// the balance is UNSAT in-circuit, not merely refused by executor arithmetic.
#[test]
fn burn_underflow_refuses() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];
    assert!(!rejects(
        &desc,
        &rows4(burn_row(&target, 1000, 600, 400, 1)),
        &burn_pis(&target, 1000, 600, 400, 1)
    ));
    // 0 - 1 wraps to u64::MAX. Trace AND PI move together, so every pin still holds.
    let bad_trace = rows4(burn_row(&target, 0, u64::MAX, 1, 1));
    let bad_pis = burn_pis(&target, 0, u64::MAX, 1, 1);
    assert!(
        rejects(&desc, &bad_trace, &bad_pis),
        "burning more than the balance must be REJECTED by the top chain gate"
    );
    assert!(
        !rejects(&drop_at(&hand_built_burn(), 54), &bad_trace, &bad_pis),
        "dropping the top chain gate flips the underflow to ACCEPT — it is the biting tooth"
    );
}

/// CANARY (revoke continuity): a value stashed in a later row → the continuity `window_gate` UNSAT.
#[test]
fn revoke_stashed_later_row_refuses() {
    let desc = parse_vm_descriptor2(REVOKE_GOLDEN).expect("decode");
    let cell = [0xAAu8; 32];
    let honest = revoke_row(&cell, 42);
    let pis = revoke_pis(&cell, 42);
    assert!(!rejects(&desc, &rows4(honest.clone()), &pis));
    let mut stashed = honest.clone();
    stashed[8] = stashed[8] + BabyBear::new(3);
    let trace = vec![honest.clone(), stashed, honest.clone(), honest];
    assert!(
        rejects(&desc, &trace, &pis),
        "a stashed later row must be REJECTED by the revoke continuity window_gate"
    );
}
