//! DEPLOYED-CONSTRAINT EVALUATOR probe + REALITY-GATE canary (game-proof LARP-audit collapse).
//!
//! Proves the `@[export] dregg_constraint_admits` symbol (over the PROVEN
//! `Dregg2.Exec.DeployedConstraint.admits`) is LINKED into `libdregg_lean.a` and that the deployed
//! node's constraint admission is COMPUTED BY THE LEAN SOURCE — not a Rust mirror. Each assertion is
//! a case the deployed `cell/src/program/eval.rs` also decides; the two the audit found DIVERGENT
//! (unsigned-256 fieldGe, first-write-free heap immutable) are pinned here as the reconciled sound
//! semantics.
//!
//! Run:  cargo test -p dregg-lean-ffi --features lean-lib --test deployed_constraint_probe -- --nocapture
//!
//! ── THE REALITY-GATE CANARY ──────────────────────────────────────────────────────────────────
//! `canary_field_gte_equal` asserts that `fieldGte` on an EQUAL value ADMITS (`>=` is non-strict).
//! To prove the deployed decision goes THROUGH this Lean source: edit
//! `metatheory/Dregg2/Exec/DeployedConstraint.lean`, flip `fieldGte`'s `if v ≤ x` to `if v < x`
//! (strict), rebuild (`cargo test -p dregg-lean-ffi --features lean-lib --test
//! deployed_constraint_probe`) — this test FLIPS RED (the equal case now REFUSES). Revert the Lean
//! and it greens. A behavior change in the linked archive caused only by a Lean-source edit is the
//! proof the evaluator is the source, not a parallel copy.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::{constraint_admits_available, shadow_constraint_admits};

const ZERO32: &str = "0000000000000000000000000000000000000000000000000000000000000000";

/// Build the admission wire: `oldPresent nonce hoP hoV hnP hnV R0..R15 N0..N15 <constraint>`.
/// `old`/`new` are 16-slot register value lists (hex); `heap` = (oldOpt, newOpt) hex options.
fn wire(
    old_present: bool,
    nonce: u64,
    heap_old: Option<&str>,
    heap_new: Option<&str>,
    old_regs: &[&str; 16],
    new_regs: &[&str; 16],
    constraint: &str,
) -> String {
    let (hop, hov) = match heap_old {
        Some(h) => ("1", h),
        None => ("0", "0"),
    };
    let (hnp, hnv) = match heap_new {
        Some(h) => ("1", h),
        None => ("0", "0"),
    };
    let mut s = format!(
        "{} {} {} {} {} {}",
        old_present as u8, nonce, hop, hov, hnp, hnv
    );
    for r in old_regs.iter() {
        s.push(' ');
        s.push_str(r);
    }
    for r in new_regs.iter() {
        s.push(' ');
        s.push_str(r);
    }
    s.push(' ');
    s.push_str(constraint);
    s
}

fn zeros16() -> [&'static str; 16] {
    [ZERO32; 16]
}

fn admits(wire: &str) -> String {
    shadow_constraint_admits(wire).expect("Lean deployed-constraint evaluator must be linked")
}

#[test]
fn evaluator_is_linked_and_live() {
    assert!(
        constraint_admits_available(),
        "dregg_constraint_admits is NOT exported by the linked archive — rebuild so build.rs splices \
         Dregg2.Exec.DeployedConstraint. (The whole collapse depends on this symbol being live.)"
    );
}

/// THE CANARY case: fieldGte on an equal value admits (`>=` non-strict). Flip the Lean `≤` to `<`
/// and this reds — the proof the archive's decision is the Lean source.
#[test]
fn canary_field_gte_equal() {
    let mut new = zeros16();
    new[0] = "5"; // hex 5
    let w = wire(false, 0, None, None, &zeros16(), &new, "FG 0 5");
    assert_eq!(
        admits(&w),
        "0",
        "fieldGte(5, 5) must ADMIT (>= is non-strict)"
    );
}

/// ⚑ RECONCILED DIVERGENCE (b): UNSIGNED 256-bit fieldGe. A value with the top bit set (2^255) is
/// >= a small threshold under the deployed unsigned compare. A signed-Int reading (the old Exec bug)
/// would treat 2^255 as "negative" and REFUSE — so this case distinguishes the two semantics.
#[test]
fn unsigned_field_gte_top_bit() {
    let mut new = zeros16();
    new[0] = "8000000000000000000000000000000000000000000000000000000000000000"; // 2^255
    let w = wire(false, 0, None, None, &zeros16(), &new, "FG 0 1");
    assert_eq!(
        admits(&w),
        "0",
        "2^255 >= 1 under UNSIGNED-256 (the reconciled semantics)"
    );
}

/// ⚑ RECONCILED DIVERGENCE (a): heap `Immutable` — the FIRST write (absent old) is FREE, then frozen.
/// The tug Lean copy's `new == old` refused the establishing write (the bug); the deployed evaluator
/// admits it.
#[test]
fn heap_immutable_first_write_free() {
    let w = wire(false, 0, None, Some("7"), &zeros16(), &zeros16(), "HIM");
    assert_eq!(
        admits(&w),
        "0",
        "heap Immutable: absent-old first write is FREE (reconciled)"
    );
}

#[test]
fn heap_immutable_frozen_after_write() {
    // old present = 7, new flips to 9 ⇒ refuse (frozen).
    let flip = wire(true, 0, Some("7"), Some("9"), &zeros16(), &zeros16(), "HIM");
    assert_eq!(
        admits(&flip),
        "1",
        "heap Immutable: a flip after the first write REFUSES"
    );
    // old = 7, new stays 7 ⇒ admit.
    let same = wire(true, 0, Some("7"), Some("7"), &zeros16(), &zeros16(), "HIM");
    assert_eq!(
        admits(&same),
        "0",
        "heap Immutable: an unchanged value ADMITS"
    );
}

/// Register-transition genesis escape + the error variants the deployed evaluator raises.
#[test]
fn error_variants_match_deployed() {
    // Immutable, old absent, nonce != 0 ⇒ TransitionCheckRequiresOldState (code 2, index 0).
    let needs_old = wire(false, 5, None, None, &zeros16(), &zeros16(), "IM 0");
    assert_eq!(admits(&needs_old), "2 0");
    // Immutable, old absent, nonce == 0 ⇒ genesis init OK.
    let genesis = wire(false, 0, None, None, &zeros16(), &zeros16(), "IM 0");
    assert_eq!(admits(&genesis), "0");
    // Index out of range ⇒ InvalidFieldIndex (code 3, index 16).
    let oob = wire(false, 0, None, None, &zeros16(), &zeros16(), "FE 16 0");
    assert_eq!(admits(&oob), "3 16");
}

/// PERF: measure the FFI admission cost per constraint (String marshal + C bridge + Lean parse+eval).
/// The deployed executor pays this ONCE per pure-subset constraint on the admission path (not the
/// proving path). Reported so the "one evaluator, the Lean one" cost is on the record, not asserted.
#[test]
fn perf_ffi_admission_cost() {
    // A MEASUREMENT, not an assertion — but a measurement that did not happen must not
    // report `ok` either, or the number on the record is from a run that never took it.
    if !dregg_lean_ffi::demand_lean(
        constraint_admits_available(),
        "dregg_constraint_admits export (the FFI admission cost cannot be measured without it)",
    ) {
        return;
    }
    let mut new = zeros16();
    new[0] = "5";
    let w = wire(false, 0, None, None, &zeros16(), &new, "FG 0 5");
    // warm up
    for _ in 0..1000 {
        let _ = admits(&w);
    }
    let n = 50_000u32;
    let t0 = std::time::Instant::now();
    for _ in 0..n {
        let _ = shadow_constraint_admits(&w).unwrap();
    }
    let per = t0.elapsed().as_nanos() as f64 / n as f64;
    println!(
        "FFI constraint-admission cost: {per:.0} ns/call ({:.2} µs)",
        per / 1000.0
    );
    // Sanity ceiling: even a heavily-loaded box should be well under 1ms/call.
    assert!(
        per < 1_000_000.0,
        "FFI admission cost {per} ns/call is implausibly high"
    );
}

/// SumEquals over the low-64 lanes (the deployed `field_to_u64` reads).
#[test]
fn sum_equals_low_lane() {
    let mut new = zeros16();
    new[0] = "3"; // 3
    new[1] = "4"; // 4
                  // sum(reg0, reg1) = 7 ⇒ SE value=7 count=2 idx 0 1 ⇒ admit.
    let ok = wire(false, 0, None, None, &zeros16(), &new, "SE 7 2 0 1");
    assert_eq!(admits(&ok), "0");
    // value=8 ⇒ violated.
    let bad = wire(false, 0, None, None, &zeros16(), &new, "SE 8 2 0 1");
    assert_eq!(admits(&bad), "1");
}
