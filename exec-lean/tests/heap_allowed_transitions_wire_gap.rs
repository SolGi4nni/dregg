//! **`HeapAtom::AllowedTransitions` — the Lean arm has LANDED. This file now pins the ARM, not the
//! gap it used to measure.**
//!
//! `cell::HeapAtom::AllowedTransitions` is the deployed twin of the Lean-authored
//! `Dregg2.Games.Dungeon.Prog.HeapAtom.allowedTransitions` (the Descent's per-relic custody hop
//! table). `cell/tests/heap_allowed_transitions_lean_sourced.rs` drives both poles of the deployed
//! Rust (guest-path) evaluator against the Lean rule. This file is about the VERIFIED oracle path.
//!
//! # What changed, and what did NOT
//!
//! `metatheory/Dregg2/Exec/DeployedConstraint.lean`'s `DHeapAtom` now carries a twelfth arm,
//! `allowedTransitions (allowed : List (Nat × Nat))` (u64 lane, both sides present required — no
//! genesis escape, exactly `eval.rs`'s `HeapAtom::AllowedTransitions`), with a wire token `HAT
//! <count> <o1> <n1> …` in `parseHeapAtom`, and a PROVED round-trip
//! (`parseHeapAtom_renderHeapAllowedTransitions`, over every `allowed : List (Nat × Nat)`, not an
//! example list). **The verified Lean evaluator now decides this atom.** That is verified below by
//! calling `dregg_lean_ffi::shadow_constraint_admits` directly with a hand-built wire — i.e. asking
//! the Lean FFI export the question this file used to be unable to ask.
//!
//! What did NOT change: `exec-lean/src/constraint_oracle.rs`'s `encode_heap_atom` — another lane's
//! uncommitted WIP, out of scope here — still has no `HeapAtom::AllowedTransitions { .. } => ...`
//! arm and still `return`s `None` for it. So `LeanConstraintOracle::admits` (the path
//! `dreggnet-web-server`'s `verified_settlement.rs` actually calls) **still declines this atom**,
//! for a DIFFERENT reason than before: not because the verified decider cannot answer, but because
//! the Rust-side encoder has not yet been taught the `HAT` token that would let it ask. The
//! [`the_transition_table_atom_is_not_yet_on_the_rust_encoder`] test below pins that this is exactly
//! what remains, so THE OUTAGE DOES NOT LIFT FROM THE LEAN ARM ALONE. Closing it needs one
//! mechanical arm in `encode_heap_atom`:
//!
//! ```text
//! HeapAtom::AllowedTransitions { allowed } => {
//!     if allowed.len() > MAX_LIST { return None; }
//!     let mut s = format!("HAT {}", allowed.len());
//!     for (o, n) in allowed { s.push_str(&format!(" {o} {n}")); }
//!     s
//! }
//! ```
//!
//! (decimal, u64-lane pairs — the SAME convention `HMEM`/`HDB`/`HDE` already use, not the register
//! `AT` tag's hex full-field pairs). Once that lands, delete the "still declines" half below and add
//! the atom to `constraint_oracle_differential.rs`'s corpus instead, where both poles are held
//! against the Lean evaluator through the FULL pipeline.
//!
//! ⚑ A DECLINE IS NOT A REFUSAL AND THIS TEST DISTINGUISHES THEM. Asking the oracle and getting
//! `None` proves nothing on its own — an oracle that declined *everything* would look identical.
//! So the "still declines" case is paired with a sibling heap atom over the SAME key and the SAME
//! states that the oracle DOES answer (the CONTROL), exactly as before.

use dregg_cell::program::{ConstraintOracle, HeapAtom, StateConstraint, TransitionMeta};
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint as SC, field_from_u64};
use dregg_exec_lean::LeanConstraintOracle;

/// `>= STATE_SLOTS(16)` ⇒ the `fields_map` tail: the heap plane, which is the whole point.
const RELIC_KEY: u64 = 20;

fn heap(v: u64) -> CellState {
    let mut s = CellState::default();
    s.set_field_ext(RELIC_KEY, field_from_u64(v));
    s
}

fn ask(c: &StateConstraint, new: &CellState, old: &CellState) -> Option<Result<(), ()>> {
    LeanConstraintOracle
        .admits(c, new, Some(old), None, &TransitionMeta::wildcard())
        .map(|r| r.map_err(|_| ()))
}

/// 16 zero register tokens.
fn zeros16() -> String {
    vec!["0"; 16].join(" ")
}

/// Build the 17-token header: `oldPresent newNonce heapOldPresent heapOldHex heapNewPresent
/// heapNewHex heapOtherPresent(0) heapOtherHex(0) oldBalance(0) newBalance(0) ctxPresent(0)
/// height(0) senderPresent(0) sender(0) epochPresent(0) epoch(0) senderEpochCount(0)` — plain,
/// no context/balance/sender, exactly `DeployedConstraint.lean`'s `wireH`/`hdrPlain` shape with an
/// explicit heap old/new.
fn header(
    heap_old_present: bool,
    heap_old_hex: &str,
    heap_new_present: bool,
    heap_new_hex: &str,
) -> String {
    format!(
        "1 0 {} {heap_old_hex} {} {heap_new_hex} 0 0 0 0 0 0 0 0 0 0 0",
        if heap_old_present { 1 } else { 0 },
        if heap_new_present { 1 } else { 0 },
    )
}

/// The whole wire: header + old regs (zero) + new regs (zero) + empty cell run + constraint tag.
fn wire(hdr: &str, constraint: &str) -> String {
    format!("{hdr} {} {} 0 {constraint}", zeros16(), zeros16())
}

/// Ask the raw Lean FFI export directly with a hand-built wire, bypassing `constraint_oracle.rs`'s
/// (still `HeapAtom::AllowedTransitions`-blind) Rust encoder entirely. This is what proves the LEAN
/// ARM decides the atom, independent of whether the Rust wire has been taught to ask it yet.
fn ask_lean_directly(w: &str) -> Result<String, String> {
    dregg_lean_ffi::shadow_constraint_admits(w)
}

#[test]
fn the_lean_arm_decides_both_poles_and_the_absent_vs_present_zero_discrimination() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the heap transition-table Lean-arm measurement)",
    ) {
        return;
    }

    // ── POLE 1: the listed hop 8 -> 13 (hex `8`, `d`) ADMITS.
    let admit_wire = wire(&header(true, "8", true, "d"), "HAT 1 8 13");
    assert_eq!(
        ask_lean_directly(&admit_wire),
        Ok("0".to_string()),
        "the Lean arm must admit a transition its own table lists"
    );

    // ── POLE 2: the same origin to an UNLISTED destination (8 -> 99, hex `63`) REFUSES.
    let refuse_wire = wire(&header(true, "8", true, "63"), "HAT 1 8 13");
    assert_eq!(
        ask_lean_directly(&refuse_wire),
        Ok("1".to_string()),
        "the Lean arm must refuse a transition its own table does not list"
    );

    // ── ABSENT-KEY vs PRESENT-ZERO, the same discrimination `cell/tests/
    // heap_allowed_transitions_lean_sourced.rs` asserts on the Rust side. A table listing `(0, 13)`
    // must still refuse an ABSENT old (no genesis escape on the heap plane)…
    let absent_old_wire = wire(&header(false, "0", true, "d"), "HAT 1 0 13");
    assert_eq!(
        ask_lean_directly(&absent_old_wire),
        Ok("1".to_string()),
        "an absent old must NOT be read as the listed 0 -- that is the escape the heap plane closes"
    );
    // …while a genuinely PRESENT zero old admits the very same listed hop.
    let present_zero_wire = wire(&header(true, "0", true, "d"), "HAT 1 0 13");
    assert_eq!(
        ask_lean_directly(&present_zero_wire),
        Ok("0".to_string()),
        "present-zero old is a real 0, and the listed hop must admit"
    );
}

/// ⚠ **THE REMAINING GAP, MEASURED PRECISELY.** The Lean arm decides the atom (proved above); the
/// FULL pipeline `dreggnet-web-server` actually calls does not yet reach it, because
/// `constraint_oracle.rs`'s `encode_heap_atom` (untouched, another lane's WIP) still declines this
/// atom before any wire is built. This is a DIFFERENT failure than the one this file used to pin —
/// re-verify this test's premise (the Rust encoder arm) before treating the outage as closed.
#[test]
fn the_transition_table_atom_is_not_yet_on_the_rust_encoder() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the heap transition-table Rust-encoder measurement)",
    ) {
        return;
    }

    let (new, old) = (heap(13), heap(8));

    // ── THE CONTROL. A sibling heap atom, same key, same two states: the FULL pipeline answers.
    // Without this, the decline below is indistinguishable from a dead oracle.
    let sibling = SC::HeapField {
        key: RELIC_KEY,
        atom: HeapAtom::MemberOf {
            set: vec![13, 14, 15, 16],
        },
    };
    assert_eq!(
        ask(&sibling, &new, &old),
        Some(Ok(())),
        "the verified oracle must decide an ordinary heap atom over this key, or this file is \
         measuring an absent oracle rather than an absent Rust wire arm"
    );
    assert_eq!(
        ask(&sibling, &heap(99), &old),
        Some(Err(())),
        "the control must be able to answer NO, or `Some(Ok(()))` above is not evidence"
    );

    // ── THE REMAINING GAP. The transition table over the SAME key and the SAME states: still no
    // answer, because `encode_heap_atom` still returns `None` for this variant.
    let table = SC::HeapField {
        key: RELIC_KEY,
        atom: HeapAtom::AllowedTransitions {
            allowed: vec![(8, 13), (8, 14), (8, 15), (8, 16)],
        },
    };
    assert_eq!(
        ask(&table, &new, &old),
        None,
        "⚑ THE RUST ENCODER ARM HAS LANDED — `encode_heap_atom` can now emit `HAT`, so this decline \
         is stale. Delete this test and add the atom to `constraint_oracle_differential.rs`'s \
         corpus, where both poles are held against the Lean evaluator through the full pipeline."
    );
    // An honest hop and a forbidden one decline IDENTICALLY: the encoder is not half-deciding.
    assert_eq!(ask(&table, &heap(99), &old), None);
}
