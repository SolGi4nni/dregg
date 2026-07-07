//! # The emit-from-Lean EQUALITY GATE — the generalized effect-action binding AIR.
//!
//! Validates the `emit-from-Lean` pattern for the `effect_action` family: the binding AIR
//! `circuit/src/effect_action_air.rs::EffectActionAir` (a 32-byte field → 8 BabyBear limbs, a u64
//! amount → 2 limbs, each limb pinned to a row-0 trace column; row-continuity forcing every row to
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
//!      `effect_action_air::{encode_hash, encode_amount}`) through [`prove_vm_descriptor2`], asserts
//!      ACCEPT, and re-verifies;
//!   3. the MUTATION CANARIES — each tampers exactly one thing and asserts refusal, and each bites a
//!      NAMED constraint:
//!        * a forged public-input limb → the `pi_binding` (the full-fidelity binding tooth);
//!        * a broken `new_balance = old_balance - amount` (trace AND PI moved together, so the pin
//!          still holds) → the Burn low-limb subtraction `gate`;
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
use dregg_circuit::effect_action_air::{encode_amount, encode_hash};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

// ── The byte-identical wire strings Lean's `emitVmJson2` emits (pinned by the `#guard`s in
//    `EffectActionBindingEmit.lean`). Drift on either side breaks the Lean `#guard` or the Rust
//    `decoded == hand_built` assertion. ──
const REVOKE_GOLDEN: &str = r#"{"name":"dregg-effect-revoke-capability-v1","ir":2,"trace_width":10,"public_input_count":10,"tables":[],"constraints":[{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":0}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":3}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":6}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":7}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":8}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":9},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":9}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9}],"hash_sites":[],"ranges":[]}"#;
const BURN_GOLDEN: &str = r#"{"name":"dregg-effect-burn-v1","ir":2,"trace_width":17,"public_input_count":16,"tables":[],"constraints":[{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":0}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":3}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":6}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":7}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":8}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":9},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":9}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":10},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":10}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":11},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":11}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":12},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":12}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":13}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":14},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":14}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":15},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":15}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":16}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9},{"t":"pi_binding","row":"first","col":10,"pi_index":10},{"t":"pi_binding","row":"first","col":11,"pi_index":11},{"t":"pi_binding","row":"first","col":12,"pi_index":12},{"t":"pi_binding","row":"first","col":13,"pi_index":13},{"t":"pi_binding","row":"first","col":14,"pi_index":14},{"t":"pi_binding","row":"first","col":15,"pi_index":15},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":10},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-4294967296},"r":{"t":"var","v":16}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":11},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}},{"t":"gate","body":{"t":"var","v":15}}],"hash_sites":[],"ranges":[]}"#;

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

/// The five Burn algebraic gates (in `eval_constraints` order), over the Burn column layout
/// (old 8/9, new 10/11, amount 12/13, was_burn 14/15, borrow aux 16).
fn burn_gates() -> Vec<VmConstraint2> {
    // new_lo + amt_lo - borrow*2^32 - old_lo
    let c_lo = LeanExpr::add(
        LeanExpr::add(v(10), v(12)),
        LeanExpr::add(
            LeanExpr::mul(k(-4294967296), v(16)),
            LeanExpr::mul(k(-1), v(8)),
        ),
    );
    // new_hi + amt_hi + borrow - old_hi
    let c_hi = LeanExpr::add(
        LeanExpr::add(v(11), v(13)),
        LeanExpr::add(v(16), LeanExpr::mul(k(-1), v(9))),
    );
    // borrow*(borrow-1)
    let c_bb = LeanExpr::mul(v(16), LeanExpr::add(v(16), k(-1)));
    // was_burn_lo - 1
    let c_wl = LeanExpr::add(v(14), k(-1));
    // was_burn_hi
    let c_wh = v(15);
    vec![
        VmConstraint2::Base(VmConstraint::Gate(c_lo)),
        VmConstraint2::Base(VmConstraint::Gate(c_hi)),
        VmConstraint2::Base(VmConstraint::Gate(c_bb)),
        VmConstraint2::Base(VmConstraint::Gate(c_wl)),
        VmConstraint2::Base(VmConstraint::Gate(c_wh)),
    ]
}

/// Independently hand-build the pure-binding revoke-capability descriptor (1 field + 1 amount).
fn hand_built_revoke() -> EffectVmDescriptor2 {
    let pi = 10;
    let mut constraints: Vec<VmConstraint2> = (0..pi).map(cont_gate).collect();
    constraints.extend((0..pi).map(pi_gate));
    EffectVmDescriptor2 {
        name: "dregg-effect-revoke-capability-v1".to_string(),
        trace_width: pi,
        public_input_count: pi,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// Independently hand-build the algebraic Burn descriptor (1 field + 4 amounts + borrow aux).
fn hand_built_burn() -> EffectVmDescriptor2 {
    let width = 17;
    let pi = 16;
    let mut constraints: Vec<VmConstraint2> = (0..width).map(cont_gate).collect();
    constraints.extend((0..pi).map(pi_gate));
    constraints.extend(burn_gates());
    EffectVmDescriptor2 {
        name: "dregg-effect-burn-v1".to_string(),
        trace_width: width,
        public_input_count: pi,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ── Witness builders (the SAME encoding the hand AIR uses). ──

/// One Burn binding row (width 17): field limbs + old/new/amount/was_burn limbs + borrow aux.
fn burn_row(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; 17];
    let f = encode_hash(target);
    row[0..8].copy_from_slice(&f);
    let [o_lo, o_hi] = encode_amount(old);
    let [n_lo, n_hi] = encode_amount(new);
    let [a_lo, a_hi] = encode_amount(amount);
    let [w_lo, w_hi] = encode_amount(was_burn);
    row[8] = o_lo;
    row[9] = o_hi;
    row[10] = n_lo;
    row[11] = n_hi;
    row[12] = a_lo;
    row[13] = a_hi;
    row[14] = w_lo;
    row[15] = w_hi;
    // Borrow bit: 1 iff the low-limb subtraction underflows (old_lo < amt_lo).
    let old_lo = old & 0xFFFF_FFFF;
    let amt_lo = amount & 0xFFFF_FFFF;
    row[16] = if old_lo < amt_lo {
        BabyBear::new(1)
    } else {
        BabyBear::ZERO
    };
    row
}

/// The Burn public inputs (the 16 pinned columns = `row[0..16]`, exactly the hand AIR's
/// `EffectActionWitness::public_inputs()`).
fn burn_pis(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    burn_row(target, old, new, amount, was_burn)[0..16].to_vec()
}

/// A 4-row (power-of-two) base trace of identical rows.
fn rows4(row: Vec<BabyBear>) -> Vec<Vec<BabyBear>> {
    vec![row.clone(), row.clone(), row.clone(), row]
}

/// One revoke-capability binding row (width 10): cell_id limbs + slot limbs.
fn revoke_row(cell: &[u8; 32], slot: u64) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; 10];
    let f = encode_hash(cell);
    row[0..8].copy_from_slice(&f);
    let [lo, hi] = encode_amount(slot);
    row[8] = lo;
    row[9] = hi;
    row
}

fn revoke_pis(cell: &[u8; 32], slot: u64) -> Vec<BabyBear> {
    revoke_row(cell, slot)
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (proving refuses, panics, OR the proof fails to
/// verify); `false` iff it both proves AND verifies. Mirrors the production posture: the
/// consumer's `verify_vm_descriptor2` is the real check (`prove` self-verifies only in debug).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(())) => false,
    }
}

// ── STEP 1 — the emitted descriptors decode and equal the hand-built twins. ──

#[test]
fn effect_action_emit_decodes_to_hand_built() {
    let dr = parse_vm_descriptor2(REVOKE_GOLDEN).expect("revoke golden decodes");
    assert_eq!(dr, hand_built_revoke(), "revoke: Lean emit ≡ hand-built");
    assert_eq!(dr.trace_width, 10);
    assert_eq!(dr.public_input_count, 10);

    let db = parse_vm_descriptor2(BURN_GOLDEN).expect("burn golden decodes");
    assert_eq!(db, hand_built_burn(), "burn: Lean emit ≡ hand-built");
    assert_eq!(db.trace_width, 17);
    assert_eq!(db.public_input_count, 16);

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
    assert_eq!((n_win(&dr), n_pin(&dr), n_gate(&dr)), (10, 10, 0));
    assert_eq!((n_win(&db), n_pin(&db), n_gate(&db)), (17, 16, 5));
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
    forged[8] = forged[8] + BabyBear::new(1); // forge the slot low-limb
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
/// continuity 0..17, pi_binding 17..33, then cLo 33, cHi 34, borrow-bool 35, was_burn_lo 36,
/// was_burn_hi 37.)
#[test]
fn mutation_canaries_bite_named_teeth() {
    let target = [0x11u8; 32];
    let burn = hand_built_burn();

    // Subtraction: with cLo present, new=601 rejects; drop cLo (33) → ACCEPTS.
    let bad_sub_t = rows4(burn_row(&target, 1000, 601, 400, 1));
    let bad_sub_p = burn_pis(&target, 1000, 601, 400, 1);
    assert!(rejects(&burn, &bad_sub_t, &bad_sub_p));
    assert!(
        !rejects(&drop_at(&burn, 33), &bad_sub_t, &bad_sub_p),
        "dropping the low-limb subtraction gate flips new=601 to ACCEPT — cLo is the biting tooth"
    );

    // Disclosure: was_burn=2 rejects; drop was_burn_lo (36) → ACCEPTS.
    let bad_wb_t = rows4(burn_row(&target, 1000, 600, 400, 2));
    let bad_wb_p = burn_pis(&target, 1000, 600, 400, 2);
    assert!(rejects(&burn, &bad_wb_t, &bad_wb_p));
    assert!(
        !rejects(&drop_at(&burn, 36), &bad_wb_t, &bad_wb_p),
        "dropping the was_burn pin flips flag=2 to ACCEPT — cWasBurnLo is the biting tooth"
    );

    // PI binding: forged pi[0] rejects; drop the col-0 pin (17) → ACCEPTS.
    let honest_t = rows4(burn_row(&target, 1000, 600, 400, 1));
    let mut forged_p = burn_pis(&target, 1000, 600, 400, 1);
    forged_p[0] = forged_p[0] + BabyBear::new(1);
    assert!(rejects(&burn, &honest_t, &forged_p));
    assert!(
        !rejects(&drop_at(&burn, 17), &honest_t, &forged_p),
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
