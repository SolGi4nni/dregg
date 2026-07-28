//! The Lean and Rust `fields_root` preimages must split at the SAME key.
//!
//! ═══ THE WOUND THIS CLOSES ═══════════════════════════════════════════════════════
//! Measured 2026-07-28. `cell/src/state.rs::STATE_SLOTS` is **16**.
//! `metatheory/Dregg2/Exec/FieldsMap.lean::reservedKeys` was **8**, and it was not a
//! stale comment — it drives `isUserTailKey` (`decide (reservedKeys ≤ n)`), which
//! defines `userTail`, which defines what `fieldsRoot` commits.
//!
//! So keys **8..15** were FIXED CELLS in Rust and COMMITTED USER-MAP TAIL KEYS in Lean.
//! The two roots disagreed over an eight-key band: every Lean theorem about `fieldsRoot`
//! described a map that included keys the deployed cell holds as indexed slots.
//!
//! Rust states the boundary three times and all three agree — `STATE_SLOTS = 16`
//! ("Number of user-defined state slots per cell"); `REFUSAL_AUDIT_EXT_KEY` is documented
//! as `>= STATE_SLOTS` *so it lands in the committed `fields_map` / `fields_root`, NOT a
//! user-addressable `fields[0..15]` indexed slot*; and `N_SYSTEM_ROOTS` is "parallel to
//! (and disjoint from) the 16 user `fields[0..15]` and the `fields_root` map". Lean's own
//! docstring said it was tracking `STATE_SLOTS`. Lean was simply behind.
//!
//! ═══ WHY THIS IS A FILE READ AND NOT A LITERAL ═══════════════════════════════════
//! A test asserting `STATE_SLOTS == 16` would pin ONE side. The drift that happened is
//! the two sides moving independently, which only a check that READS BOTH can catch.
//! So this parses the Lean `def` out of the source. It is the same shape as the geometry
//! pin added for `CAP_OPEN_WIDTH` after a prose number went three flag-days stale: a
//! comment cannot go red, so the constant is compared against the other side's actual text.

use dregg_cell::state::STATE_SLOTS;

/// The Lean module that owns the reserved/user split.
const LEAN_FIELDSMAP: &str = "../metatheory/Dregg2/Exec/FieldsMap.lean";

fn lean_reserved_keys() -> usize {
    let src = std::fs::read_to_string(LEAN_FIELDSMAP).unwrap_or_else(|e| {
        panic!(
            "cannot read {LEAN_FIELDSMAP}: {e}. This pin compares the DEPLOYED Rust constant \
             against the Lean source that defines the same split; if the module moved, re-point \
             it rather than deleting the check — an unread pin is the drift it exists to catch."
        )
    });
    // `def reservedKeys : Nat := N`, tolerating whitespace. Deliberately NOT a loose grep for
    // the identifier: it appears in a dozen doc comments in that file, and matching prose is
    // how a reader reports a number nobody wrote.
    let line = src
        .lines()
        .find(|l| l.trim_start().starts_with("def reservedKeys"))
        .expect("no `def reservedKeys` in the Lean module — the definition was renamed or removed");
    line.rsplit(":=")
        .next()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .unwrap_or_else(|| panic!("could not parse a Nat out of: {line:?}"))
}

#[test]
fn lean_and_rust_split_fields_root_at_the_same_key() {
    let lean = lean_reserved_keys();
    assert_eq!(
        lean,
        STATE_SLOTS,
        "\nTHE `fields_root` PREIMAGES SPLIT AT DIFFERENT KEYS.\n\
         \n  Rust  cell/src/state.rs::STATE_SLOTS               = {STATE_SLOTS}\n  \
           Lean  Dregg2/Exec/FieldsMap.lean::reservedKeys      = {lean}\n\n\
         Keys in [{lo}..{hi}) are fixed cells on one side and committed user-map tail keys on \
         the other, so `fieldsRoot` commits a different set than the deployed cell holds, and \
         every Lean theorem about it describes a map the executor never builds.\n\n\
         `reservedKeys` is not documentation: it drives `isUserTailKey` -> `userTail` -> \
         `fieldsRoot`. Move the Lean `def` to match `STATE_SLOTS` (and move any `#guard` \
         fixture keys above the new band), or change Rust and then this line.\n",
        lo = lean.min(STATE_SLOTS),
        hi = lean.max(STATE_SLOTS),
    );
}

#[test]
fn the_pin_reads_a_real_definition_and_not_prose() {
    // ANTI-VACUITY. `reservedKeys` occurs in ~10 doc comments in that module. If the reader
    // ever matches one of those instead of the `def`, this test would still "find" a number
    // and the pin above would compare something nobody wrote. Assert we landed on a `def`
    // whose value parses, and that the module really does mention the identifier many times —
    // so a future loosening of the matcher is caught here rather than silently.
    let src = std::fs::read_to_string(LEAN_FIELDSMAP).expect("Lean module readable");
    let mentions = src.matches("reservedKeys").count();
    assert!(
        mentions >= 5,
        "expected `reservedKeys` to appear many times (docs + def); found {mentions}. \
         If the module shrank this much, re-read it before trusting the pin."
    );
    let defs = src
        .lines()
        .filter(|l| l.trim_start().starts_with("def reservedKeys"))
        .count();
    assert_eq!(
        defs, 1,
        "expected exactly one `def reservedKeys`, found {defs}"
    );
    assert!(
        lean_reserved_keys() > 0,
        "a zero reserved band would make every key a tail key"
    );
}
