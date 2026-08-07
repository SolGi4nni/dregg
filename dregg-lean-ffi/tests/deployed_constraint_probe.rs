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
//!
//! ── ⚑ AND THE CANARY WAS ASLEEP FOR A WEEK (measured 2026-08-07) ─────────────────────────────
//! A canary is only a canary if the wire it sends is one the CURRENT evaluator parses. The
//! admission header grew from 6 tokens to 17 between 2026-07-30 and 08-01 (`heapOther`, the balance
//! pair, the four context fields, and a resolved cell run); this file's builder was last touched
//! 2026-07-27 and still emitted the six-token shape. Six of these eight tests were therefore
//! asserting against `parse = none`, which `admitsWire` THEN rendered as `"1"` — the SAME string as
//! a genuine refusal. They did not go red at the time because the archive linked on this box carried
//! a **2026-07-25** `Dregg2_Exec_DeployedConstraint.o`: the builder and the evaluator were wrong
//! together, and agreement between two stale things reads exactly like correctness. Re-splicing the
//! archive refreshed the evaluator alone and the six reds appeared.
//!
//! Three things changed so it cannot recur silently: `tests/linked_archive_freshness.rs` refuses an
//! archive whose Dregg2 objects predate their `.lean` sources (it names
//! `Dregg2_Exec_DeployedConstraint.o` on the seed in this checkout);
//! `wire_arity_is_the_current_lean_wire` below pins the grammar on verdicts a parse failure
//! CANNOT produce, instead of on agreement; and — the repair for the class rather than the
//! instance — **an unreadable wire now has its own code.**
//!
//! ── THE REPRESENTATION COLLISION IS CLOSED (2026-08-07) ──────────────────────────────────────
//! `Dregg2.Exec.DeployedConstraint.admitsOutcome` returns a `DWireOutcome`, whose `malformed` arm
//! is not a `DAdmit` at all, so no evaluation path can produce it. It renders `"7 <stage>"` where
//! `<stage>` is the `DWireFault` the parse stopped at, and `exec-lean`'s `decode_verdict` maps it
//! to `ProgramError::ConstraintOracleWireMalformed` — so the DEPLOYED node's diagnosis names the
//! Rust/Lean wire disagreement instead of naming the player's constraint. The two poles are Lean
//! theorems over every wire (`admitsWire_eq_violated_iff`, `admitsWire_malformed_iff`), and
//! [`a_malformed_wire_is_distinguishable_from_a_violation`] below asserts them through the LINKED
//! ARCHIVE, which is the only place that can tell you what this binary will actually do.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::{constraint_admits_available, shadow_constraint_admits};

const ZERO32: &str = "0000000000000000000000000000000000000000000000000000000000000000";

/// The number of HEADER tokens `Dregg2.Exec.DeployedConstraint.parseE` pops before the two
/// 16-register runs — the Lean side's `headerTokens`. Named here because it is the ONE number a
/// wire-arity drift moves. Getting it wrong used to be INVISIBLE (`admitsWire` rendered an
/// unparseable wire as `"1"`, the same string as a genuine `ConstraintViolated`); it is now
/// [`MALFORMED_TAG`]-visible, and `wire_arity_is_the_current_lean_wire` reads it directly.
const HEADER_TOKENS: usize = 17;

/// The first token of `Dregg2.Exec.DeployedConstraint.renderOutcome (.malformed f)` — the code a
/// wire that DID NOT PARSE renders as, and which no verdict of a successful evaluation can produce
/// (`render_ne_malformed`, over every `DAdmit` and every `DWireFault`).
const MALFORMED_TAG: &str = "7";

/// `DWireFault.headerArity` — fewer than [`HEADER_TOKENS`] tokens on the wire at all.
const FAULT_HEADER_ARITY: &str = "7 0";
/// `DWireFault.cellCount` — the resolved-cell-run count token is not decimal.
///
/// ⚑ This is where a wire ONE TOKEN SHORT lands, and the reason is worth knowing: the 17 header
/// tokens are almost all `0` on a neutral wire, so shifting the stream by one still DESTRUCTURES
/// and still parses — every field is a `0`, and the 64-zero register hex that slides into the
/// `sender_epoch_count` slot parses as decimal `0` too. Both 16-token register runs then absorb the
/// shift (a `0` is valid hex), and the drift only surfaces at the cell-count token, where a register
/// hex or a constraint tag lands. A positional token grammar over a mostly-zero header cannot detect
/// its own arity locally; the fault code is what makes the failure legible at all.
const FAULT_CELL_COUNT: &str = "7 5";
/// `DWireFault.constraintTag` — the header, both register runs and the cell run parsed; the
/// constraint tag did not. This is where an unknown tag lands, and where a wire one token LONG does.
const FAULT_CONSTRAINT_TAG: &str = "7 7";

/// True when `out` is the malformed-wire code rather than a verdict.
fn is_malformed(out: &str) -> bool {
    out.split_whitespace().next() == Some(MALFORMED_TAG)
}

/// Build the admission wire — the SAME grammar `exec-lean/src/constraint_oracle.rs::build_wire`
/// emits on the deployed admission path, and the one
/// `Dregg2.Exec.DeployedConstraint.parse`/`parseHeader`/`parseCells` reads:
///
/// ```text
/// oldPresent nonce  hoP hoV  hnP hnV  hxP hxV  oldBal newBal
/// ctxP height  sndP sender  epP epoch  epochCount        (17 header tokens)
/// R0..R15  N0..N15  <ncells> (present value)*ncells  <TAG> args…
/// ```
///
/// ⚑ THIS BUILDER WAS SIX HEADER TOKENS UNTIL 2026-08-07 AND EVERY ASSERTION BELOW WAS ABOUT A
/// WIRE THE EVALUATOR REFUSED TO PARSE. The header grew from 6 tokens to 17 over 2026-07-30..08-01
/// (heapOther, the balance pair, the four context fields, and the resolved cell run); this test's
/// builder was last touched on 07-27. It kept reporting `ok` for a week because the archive linked
/// on this box carried a 2026-07-25 `Dregg2_Exec_DeployedConstraint.o` — the six-token evaluator —
/// so the builder and the evaluator were consistently wrong together. `linked_archive_freshness`
/// is the gate that now refuses that pairing.
///
/// `old`/`new` are 16-slot register value lists (hex); `heap` = (oldOpt, newOpt) hex options. The
/// remaining header fields are the neutral values the deployed builder emits when the constraint
/// does not read them (no third heap key, zero balances, absent context) — the arms exercised here
/// are register/heap arms, and an arm that DOES read context raises `missingContext` (code 4),
/// which `error_variants_match_deployed` pins.
fn wire(
    old_present: bool,
    nonce: u64,
    heap_old: Option<&str>,
    heap_new: Option<&str>,
    old_regs: &[&str; 16],
    new_regs: &[&str; 16],
    constraint: &str,
) -> String {
    fn opt(v: Option<&str>) -> String {
        match v {
            Some(h) => format!("1 {h}"),
            None => "0 0".to_string(),
        }
    }
    // 17 header tokens. The three `opt(..)` renderings are TWO tokens each (presence + value),
    // so `6 + 3*2 + 5 = 17` — the count `HEADER_TOKENS` names and `parseHeader` destructures.
    let mut s = format!(
        "{} {} {} {} {} {} {} {} {} {} {} {} {}",
        old_present as u8, // oldPresent
        nonce,             // newNonce
        opt(heap_old),     // hoP hoV
        opt(heap_new),     // hnP hnV
        opt(None),         // hxP hxV — no third heap key on any case here
        0,                 // oldBalance
        0,                 // newBalance
        0,                 // ctxPresent
        0,                 // height
        0,                 // senderPresent
        0,                 // sender
        0,                 // epochPresent
        0,                 // epoch
    );
    s.push_str(" 0"); // epochCount — the 17th token
    for r in old_regs.iter() {
        s.push(' ');
        s.push_str(r);
    }
    for r in new_regs.iter() {
        s.push(' ');
        s.push_str(r);
    }
    s.push_str(" 0"); // the RESOLVED CELL RUN: zero cells (no `FCE`/`CAGG` case here)
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

/// ⚑ THE WIRE-ARITY TOOTH, and it is not decoration — it is the assertion whose absence let this
/// whole file report `ok` on a wire the evaluator never parsed, for a week.
///
/// It was built from the two verdicts a PARSE FAILURE CANNOT PRODUCE, because at the time a parse
/// failure and a violation were the same string:
///   * `"3 16"` — `InvalidFieldIndex 16`, reachable only after the header, both register runs and
///     the cell run have been consumed and `FE 16 0` has been read as a constraint;
///   * `"2 0"`  — `TransitionCheckRequiresOldState`, which needs `oldPresent`/`nonce` decoded.
///
/// Both legs are kept — a positive verdict is still the strongest evidence that the whole wire was
/// consumed — but the short/long legs now assert the MALFORMED CODE by value instead of `"1"`,
/// which is the repair rather than the workaround.
#[test]
fn wire_arity_is_the_current_lean_wire() {
    if !dregg_lean_ffi::demand_lean(
        constraint_admits_available(),
        "dregg_constraint_admits export (the wire arity cannot be probed without it)",
    ) {
        return;
    }
    let w = wire(false, 0, None, None, &zeros16(), &zeros16(), "FE 16 0");
    let tokens: Vec<&str> = w.split_whitespace().collect();
    assert_eq!(
        tokens.len(),
        HEADER_TOKENS + 16 + 16 + 1 + 3,
        "the builder emitted {} tokens; the grammar is {HEADER_TOKENS} header + 16 old regs + \
         16 new regs + 1 cell-run count + the 3-token `FE 16 0` constraint",
        tokens.len()
    );

    // A wire that PARSED — `"3 16"` is unreachable from a parse failure, which renders `"7 …"`.
    assert_eq!(
        admits(&w),
        "3 16",
        "the evaluator did not reach `InvalidFieldIndex` — this wire did not parse. Reconcile this \
         builder with `Dregg2.Exec.DeployedConstraint.parseHeader` (and with \
         `exec-lean/src/constraint_oracle.rs::build_wire`, which emits the deployed wire)."
    );

    // ...and the arity is load-bearing in BOTH directions. These used to assert `"1"` — the string
    // a genuine `ConstraintViolated` also renders as — so they held whether or not the evaluator
    // had a distinct answer for "this is not a wire I can read". They now name the fault STAGE.
    let short = {
        let mut t = tokens.clone();
        t.remove(0);
        t.join(" ")
    };
    let short_out = admits(&short);
    assert!(
        is_malformed(&short_out),
        "a wire one token SHORT must report the MALFORMED code, not a verdict — it answered \
         {short_out:?}. This is the drift this test exists to catch, and asserting `\"1\"` here \
         (which is what it used to do) could not tell the drift from a correct refusal."
    );
    assert_eq!(short_out, FAULT_CELL_COUNT);
    let long = format!("0 {w}");
    let long_out = admits(&long);
    assert!(
        is_malformed(&long_out),
        "a wire one token LONG must report the MALFORMED code, not a verdict — it answered \
         {long_out:?}"
    );
    assert_eq!(long_out, FAULT_CONSTRAINT_TAG);
}

/// ⚑ **THE REPAIR, ASSERTED THROUGH THE LINKED ARCHIVE — BOTH POLES.**
///
/// The Lean theorems (`admitsWire_eq_violated_iff`, `admitsWire_malformed_iff`) are about the
/// source. This is about the `.o` this binary linked, which is the thing that decides turns, and
/// which spent a week being a different program from the source (see this file's header).
///
/// Pole 1 — a GENUINE constraint violation still reports `"1"`. Without it, "malformed and
/// violation differ" is satisfied by an evaluator that calls everything malformed.
/// Pole 2 — a short, a long and a garbage wire each report the malformed code, never `"1"`.
///
/// Each mutation is asserted PRESENT before its verdict is read: a short wire that is not actually
/// shorter, or a garbage wire that happens to parse, would make the pole below it vacuous in
/// exactly the way this whole file was vacuous.
#[test]
fn a_malformed_wire_is_distinguishable_from_a_violation() {
    if !dregg_lean_ffi::demand_lean(
        constraint_admits_available(),
        "dregg_constraint_admits export (the malformed/violated separation cannot be probed \
         without it)",
    ) {
        return;
    }

    // ── POLE 1: a wire that PARSES and whose constraint is genuinely violated. new[0] = 0, the
    // constraint demands 5.
    let violated = wire(false, 0, None, None, &zeros16(), &zeros16(), "FE 0 5");
    assert_eq!(
        admits(&violated),
        "1",
        "a genuine ConstraintViolated must still report `\"1\"` — if it does not, the separation \
         below is meaningless and the deployed decoder's `ConstraintViolated` arm is dead"
    );
    // ...and the SAME wire with the constraint satisfied admits, so the `"1"` above is the
    // constraint's doing and not the wire's.
    let admitted = wire(false, 0, None, None, &zeros16(), &zeros16(), "FE 0 0");
    assert_eq!(
        admits(&admitted),
        "0",
        "the control wire must ADMIT — otherwise the `\"1\"` above could be any refusal at all"
    );

    // ── POLE 2a: ONE TOKEN SHORT. The mutation is asserted present first.
    let full: Vec<&str> = violated.split_whitespace().collect();
    let short = full[1..].join(" ");
    assert_eq!(
        short.split_whitespace().count(),
        full.len() - 1,
        "the SHORT mutation did not remove a token — the assertion below would be about the \
         unmutated wire, which is exactly how a falsifier stops falsifying"
    );
    assert_eq!(
        admits(&short),
        FAULT_CELL_COUNT,
        "a wire one token short must report a MALFORMED code — see FAULT_CELL_COUNT for why the \
         stage is the cell-count token and not the header"
    );

    // ── POLE 2b: GARBAGE. One token, so it cannot reach the header at all — the only input here
    // that fails the arity check itself.
    assert_eq!(
        admits("garbage"),
        FAULT_HEADER_ARITY,
        "a one-token wire must report the header-arity fault"
    );

    // ── POLE 2c: A WELL-FORMED WIRE WITH AN UNKNOWN CONSTRAINT TAG — the shape a Rust/Lean tag
    // drift actually takes, and the one a length check cannot see. The header, both register runs
    // and the cell run all parse; only the tag does not.
    let bad_tag = wire(false, 0, None, None, &zeros16(), &zeros16(), "NOPE 1 2");
    assert_eq!(
        bad_tag.split_whitespace().count(),
        full.len(),
        "the bad-tag wire must be the SAME length as the good one, or this leg is just the short \
         case again"
    );
    assert_eq!(
        admits(&bad_tag),
        FAULT_CONSTRAINT_TAG,
        "an unknown constraint tag on an otherwise valid wire must report the constraint-tag \
         fault — NOT `\"1\"`, which is what a node with a drifted marshaller used to report to \
         every player for every turn"
    );

    // ── AND THE POINT, stated as the comparison it is.
    assert_ne!(
        admits(&bad_tag),
        admits(&violated),
        "a wire the evaluator could not read and a constraint it refused must not be the same \
         value — that collision is the defect this test exists for"
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
    // ⚑ The number on the record must be the cost of an ADMISSION, not the cost of a parse
    // failure. Until 2026-08-07 this measured the latter and still printed a plausible figure.
    assert_eq!(
        admits(&w),
        "0",
        "the perf wire does not admit — this would time `parse = none`, not an admission"
    );
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
