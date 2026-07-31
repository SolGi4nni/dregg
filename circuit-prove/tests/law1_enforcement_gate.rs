//! **LAW #1 RATCHET** — the systematic enforcement of "zero Rust-authored constraints or AIRs, ever".
//!
//! `metatheory/README.md:15` states architectural law #1: *"Circuits are **emitted from Lean**... Rust only
//! INTERPRETS those artifacts. A coverage gap is closed by emitting from a new proved module, **never** by
//! hand-authoring a constraint."* Until this gate existed the law lived only in PROSE — and prose does not
//! fail a build.
//!
//! ## What this gate looks at (2026-07-25 rewrite — read this before trusting a number)
//!
//! The previous revision of this file was **blind in two directions at once**, and the two blindnesses
//! compounded: it scanned only `circuit/src` + `circuit-prove/src`, and within that scope it counted
//! `ConstraintExpr::` *textually*, which counts `match` PATTERNS as if they were authored algebra.
//!
//! * **Scope.** The single largest hand-written Rust AIR in the tree — `param-compose/src/air.rs` +
//!   `param-compose/src/builder.rs`, ~1000 lines, its own `Head` polynomial type, its own
//!   `assert_zero`, its own `air_accepts`, and a `tamper()` forgery harness — sat entirely OUTSIDE the
//!   scanned directories and was therefore invisible to a gate whose entire purpose is to see it. At
//!   the time of that rewrite it was live on a production path (`entity-compose/src/lib.rs` imported
//!   `dregg_param_compose::air::{ComposeAir, build}` in non-test code), both crates are workspace
//!   `default-members`, and `metatheory/` contained **no** `paramCompose` emitter. This gate now scans
//!   **every `.rs` file under any `src/` tree in the repository**, so a violation cannot hide by being
//!   in a different crate. **OUTCOME (2026-07-25): both files are DELETED.** Lean grew the route
//!   (`Dregg2/Circuit/Emit/ParamComposeEmit.lean` + `ParamComposeRefine`, all 18 corpus shapes
//!   `#guard`-pinned), the consumers and the whole test corpus moved onto the emitted descriptor, and
//!   the two `BASELINE` rows went with the files.
//! * **Counting.** `circuit/src/custom_leaf_lowering.rs` "violated" the old gate 46 times. Every one of
//!   those 46 is `ConstraintExpr::Variant { .. } =>` — a match arm in a LOWERING. Destructuring a
//!   constraint authors nothing. A gate that cries wolf 46 times gets ignored, and this one was: the
//!   previous revision, compiled and run against the tree it shipped with, **exited 101 — RED at HEAD**,
//!   its largest single "violation" being those 46 non-violations. Nobody noticed because the CI job
//!   that runs it (`cargo test --workspace`, `.github/workflows/ci.yml` Test (macos/ubuntu)) has been
//!   dying while compiling `dregg-lean-ffi`'s BUILD SCRIPT — ten `E0433`/`E0425`s against
//!   `build_parallel` — so the test binary is never linked and the gate never executes. A red gate
//!   nobody sees and a gate that does not run are the same object. So the gate now **classifies
//!   construction against destructuring** rather than grepping.
//!
//! ## The FIVE constraint dialects
//! A grep for one dialect sees a fifth of the truth. Miss one and you will miscount — that is the whole
//! point of this gate. In dependency order of how easy they are to overlook:
//!
//!   1. **plonky3 symbolic** — `x.assert_zero(..)` on ANY receiver. The previous revision hard-coded the
//!      receiver name `builder`, so `b.assert_zero(&Head::lin(..))` (param-compose's whole AIR, 19 sites)
//!      and `tb`/`lb`/`fb`/`self` receivers were unmatched. Receiver-agnostic now.
//!      `.assert_eq(..)` and `.when*(..)` join it ONLY in a file that mentions `AirBuilder` — `when` is a
//!      constraint dialect only in an AirBuilder context, and without that guard every gpui
//!      `.when(cond, ..)` in `starbridge-v2/src/cockpit/*` becomes a fake AIR violation.
//!   2. **closures** — `eval: Box::new(|row, _, pi| ..)`. Invisible to (1).
//!   3. **`ConstraintExpr` literals** — the DSL descriptor algebra. Invisible to (1) and (2).
//!   4. **descriptor gate trees** — `LeanExpr` / `VmConstraint` / `VmConstraint2` values built directly in
//!      Rust. This is the dialect that let a file truthfully say it "authors NO constraints" while
//!      authoring the entire descriptor: `circuit-prove/src/shielded_ring_clearing_air.rs` builds 75 of
//!      them with no `include_str!` and no `parse_vm_descriptor2` anywhere in the file, and `perf/src/lib.rs`
//!      hand-builds a `VmConstraint2::MapOp` / `UMemOp` descriptor in a crate the old scope never reached.
//!   5. **`air_accepts` predicates** — a Rust-authored answer to "does the AIR accept this row". The law
//!      names these explicitly; they get their own ledger below (`AIR_ACCEPTS_LEDGER`) and their own test.
//!
//! ## AUTHORING vs LOWERING — the distinction, in code, not in an exclusion list
//! For dialects (3) and (4) the same text `ConstraintExpr::Binary { col }` is either **construction**
//! (algebra originates here — authoring) or **destructuring** (algebra arrived from somewhere else and is
//! being read — lowering / interpreting). `classify_site` decides it syntactically:
//!
//! * a `..` rest inside the braces is pattern-only (a struct-update base in an expression must be
//!   `..expr`, never bare `..`),
//! * a following `=>` (optionally through an `if` guard) or a following `|` is a match arm,
//! * `matches!(`, `if let`, `while let`, `let .. =` in binding position are patterns,
//! * anything else constructs.
//!
//! This is the *only* exclusion in the gate and it is a property of the source text, not a list of
//! forgiven filenames. It takes `custom_leaf_lowering.rs` from 46 phantom violations to 0 — while still
//! counting the 64 `LeanExpr` nodes that file really does construct, because a lowering that authors
//! `x·(x−1)` for `Binary` **is** authoring that algebra in Rust; that is exactly the debt
//! `CustomLeafEncoding.lean::cell_to_descriptor_faithful` exists to discharge. Destructuring is free;
//! construction is counted wherever it happens.
//!
//! ## `#[cfg(test)]` INSIDE a `src/` file is COUNTED — and that is not an accident (2026-07-30)
//! The scope test is `rel.contains("/src/")`, so the gate's "test code is not ratcheted" decision is
//! implemented as a **directory** property. That proxy is wrong in exactly one direction: a
//! `#[cfg(test)] mod tests` inside a `src/` file is test code that the directory test calls
//! production, and identical source text therefore scores 8 in `circuit-prove/src/foo.rs` and 0 in
//! `circuit-prove/tests/foo.rs`.
//!
//! **The strictness EARNED ITS KEEP, so it stays.** On 2026-07-30 the gate went red on
//! `circuit-prove/src/dregg_mina_config.rs` — 8 sites, 8 symbolic, all inside `#[cfg(test)]`, and all
//! of them a byte-identical THIRD copy of the toy Fibonacci AIR that `dregg_outer_config::tests` and
//! `gpu_backend::tests` already each carried. None of it was dregg constraint content; the file's own
//! module doc opened with "no AIR, no constraint, no gadget" and was, on the plumbing question,
//! correct. It was still a hand-written Rust AIR, and law #1's own words are that an existing Rust AIR
//! is debt rather than a foundation, so copying one **is** the drift. Had `#[cfg(test)]` been free,
//! that third copy would have landed silently and a fourth would have followed. The fix was
//! subtraction — three copies became one shared `dregg_outer_config::toy_fib_air` — and this gate was
//! not touched to make it green.
//!
//! What DID change is that `cfg_test_regions` now ATTRIBUTES sites, so a failure message can say
//! "ALL 8 inside `#[cfg(test)]`" instead of leaving the reader to open the file and guess whether the
//! gate mis-fired. Attribution only: `authored()` is unchanged, and `#[cfg(any(test, feature = ..))]`
//! deliberately does not count as test-only because that item ships whenever the feature is on.
//!
//! **The asymmetry's correct resolution is to close the `tests/` hole, not to widen the `src/`
//! exemption** — the direction of the law is fewer Rust-authored constraints, and the hole is the
//! looser side. That is a campaign, not a line: 847 sites across 41 files, most of them legitimate
//! emit-gate differentials that must be separated from the rest before any of it can be ratcheted.
//! **First rung, named so it is findable:** classify `tests/` sites into (a) differentials that build
//! a Rust expectation *and compare it against a Lean emission in the same file* — the law working —
//! and (b) everything else, then ratchet (b) alone. Until that exists, the bullet below stands.
//!
//! ## What this gate CANNOT see (say it out loud rather than imply coverage)
//! * **`tests/` trees.** 41 test files author 847 sites — overwhelmingly emit-gate differentials,
//!   which must build a Rust-side expectation in order to compare it against the Lean emission (that is
//!   the law working). They are not ratcheted here, so a hand-written AIR parked in a `tests/` directory
//!   is invisible to this gate. Scoped out deliberately, named as a hole. ⚑ And it is the LOOSER side
//!   of the `#[cfg(test)]` asymmetry above: moving a counted `src/` AIR into `tests/` would zero its
//!   score without deleting a line, which is laundering, not a fix.
//! * **Semantics.** The count is IR *nodes constructed*, not constraint *degree* or *soundness*. It is a
//!   monotone proxy: more Rust-authored algebra ⇒ a bigger number. It says nothing about whether a
//!   constraint is right, and a file can restructure to lower its number without emitting from Lean.
//! * **Indirection.** Algebra built through a helper that takes the variant as data (a `Vec<PolyTerm>`
//!   assembled far from any `ConstraintExpr::`) is undercounted; only the final constructor is seen.
//! * **Non-Rust hosts.** Solidity, Lean-adjacent scripts, and generated code under `target/` are out of
//!   scope, as are `docs/` snapshots of Rust (there is a byte-identical copy of `descriptor_ir2.rs` under
//!   `docs/deos/artifacts/` that is documentation, not a compiled unit).
//! * **`metatheory/`** is skipped entirely — that is where the algebra is SUPPOSED to live.
//!
//! ## If this test fails
//! You (or an agent) hand-authored a constraint in Rust. That is the violation itself — do NOT add your
//! file to the baseline to make it green. Emit it from Lean instead (`metatheory/Dregg2/Circuit/Emit/*.lean`
//! -> `emitVmJson2` -> `descriptors/by-name/*.json` -> `descriptor_by_name` -> `prove_vm_descriptor2`; see
//! `EffectVmEmitTurnChainBinding.lean` + `metatheory/EmitTurnChain.lean` for the worked end-to-end example).
//! Lower the baseline when you retire algebra; raise it only with a recorded reason in GOAL-STARK-KILL.md.
//! `LAW1_PRINT_BASELINE=1 cargo test -p dregg-circuit-prove --test law1_enforcement_gate -- --nocapture`
//! prints the current ledger in source form, so a legitimate SHRINK is a copy-paste.
//!
//! ## Why entries remain (the honest ledger, not an amnesty)
//! * INTERPRETERS (the law WORKING — they evaluate Lean-authored constraints): `descriptor_ir2.rs`,
//!   `descriptor_ir2_canonical.rs`, `dsl/dsl_p3_air.rs`, `lean_lookup_air.rs` (the proven range gadget).
//!   Their *pattern* halves are now free; the residual is the IR they construct while translating.
//! * PROVED-FAITHFUL LOWERINGS: `custom_leaf_adapter.rs` / `custom_leaf_lowering.rs` —
//!   `CustomLeafEncoding.lean::cell_to_descriptor_faithful` proves the encoding preserves semantics.
//! * DRIFT-DETECTORS, deliberately kept: `dsl/derivation.rs`, `dsl/note_spending.rs` — the EMITTED paths
//!   walk these v1 descriptors as their SOURCE, so "a drift in the deployed circuit is a build-time
//!   refusal, never a silent divergence" (`note_spend_witness.rs:225-227`).
//! * THE USER-PROGRAM GRAMMAR: `dsl/predicates/*`, `dsl/descriptors.rs` — the host-trusted smart-contract
//!   surface users deploy programs against; interpreted, fails closed on an unknown vk_hash.
//! * THE ONE TEST-ONLY TOY AIR: `dregg_outer_config.rs` (8) — `toy_fib_air::ToyFibAir`, the p3
//!   uni-stark 2-column Fibonacci, `#[cfg(test)]`-gated and shared by all three configs in the crate
//!   (CPU outer, GPU outer, Mina terminal). A `StarkConfig` round-trip needs *an* AIR to prove and it
//!   must deliberately not be a dregg one. Was THREE copies until 2026-07-30; `gpu_backend.rs` (8) and
//!   a fresh `dregg_mina_config.rs` (8) are both retired into this row.
//! * NAMED RESIDUALS — real debt, now VISIBLE for the first time:
//!   - ~~**`param-compose/src/{air,builder}.rs` (28) + the `entity-compose` consumer.**~~ **CLOSED
//!     2026-07-25 — DELETED, 1028 lines.** It was a complete hand-written Rust AIR: 24 `assert_zero`
//!     sites, its own `ConstraintExpr` emission, `air_accepts`, and `tamper()`, and `builder.rs`
//!     documented itself as "a sibling of `dregg-automatafl`'s builder … duplicated rather than
//!     shared" — the automatafl Rust-AIR deletion was recorded as complete, but the clone had already
//!     been copied out into `param-compose/`, where it survived precisely because it was outside this
//!     gate's old scope. The "There is NO Lean route" line this entry carried is what changed:
//!     `Dregg2/Circuit/Emit/ParamComposeEmit.lean` now authors the whole AIR and byte-pins the wire,
//!     `ParamComposeRefine.paramCompose_refines_law` refines it, and all 18 shapes the test corpus
//!     exercises are `#guard`-pinned, so consumers and tests alike ride the emitted descriptor.
//!     Deleting it was the fix; this line is the receipt that it happened. (The honest price — four
//!     coverage items that lost their only checker — is recorded in `param-compose/src/lib.rs`.)
//!   - **`perf/src/lib.rs` (28)** — a hand-built `VmConstraint2::{MapOp,UMemOp}` descriptor, dialect (4),
//!     in a crate no previous audit scanned.
//!   - `ivc.rs` + `dsl/fold.rs` (`FoldAir`) — test-only; `ivc`'s emitter is one Lean PROVES insufficient
//!     (`ivc_anchor_insufficient`).
//!   - `dregg-dsl-differential/*`, `dregg-dsl-runtime/src/composition.rs`, `constraint-lowering/src/lib.rs`,
//!     `game-turn-slice/src/compiler.rs`, `sdk/src/full_turn_proof.rs`, `turn/src/umem.rs`,
//!     `tests/src/dsl_pipeline.rs` — the rest of the surface the two-directory scope hid.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

// ─────────────────────────────────────────────────────────────────────────────
// Lexical normalisation. Comments and string bodies are blanked (newlines kept, so
// byte offsets and line numbers survive) — otherwise this gate's OWN module docs,
// and every `"ConstraintExpr::Foo"` in an error message, would count as algebra.
// ─────────────────────────────────────────────────────────────────────────────
fn blank_noncode(src: &str) -> String {
    let b = src.as_bytes();
    let n = b.len();
    let mut out = Vec::with_capacity(n);
    let mut i = 0usize;
    // Copy `k` bytes as blanks, preserving newlines so offsets->lines stay honest.
    macro_rules! blank_to {
        ($j:expr) => {{
            let j = $j;
            for &c in &b[i..j] {
                out.push(if c == b'\n' { b'\n' } else { b' ' });
            }
            i = j;
        }};
    }
    while i < n {
        let c = b[i];
        if c == b'/' && i + 1 < n && b[i + 1] == b'/' {
            let j = b[i..].iter().position(|&c| c == b'\n').map_or(n, |p| i + p);
            blank_to!(j);
        } else if c == b'/' && i + 1 < n && b[i + 1] == b'*' {
            // Rust block comments nest.
            let mut depth = 0usize;
            let mut j = i;
            while j < n {
                if b[j] == b'/' && j + 1 < n && b[j + 1] == b'*' {
                    depth += 1;
                    j += 2;
                } else if b[j] == b'*' && j + 1 < n && b[j + 1] == b'/' {
                    depth -= 1;
                    j += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    j += 1;
                }
            }
            blank_to!(j.min(n));
        } else if c == b'r' && !prev_is_ident(b, i) && raw_string_hashes(b, i).is_some() {
            let h = raw_string_hashes(b, i).unwrap();
            // r{#*}" .. "{#*}
            let open_end = i + 1 + h + 1;
            let mut close = String::from("\"");
            close.push_str(&"#".repeat(h));
            let j = find(b, open_end, close.as_bytes()).map_or(n, |p| p + close.len());
            blank_to!(j);
        } else if c == b'"' {
            let mut j = i + 1;
            while j < n {
                if b[j] == b'\\' {
                    j += 2;
                    continue;
                }
                if b[j] == b'"' {
                    j += 1;
                    break;
                }
                j += 1;
            }
            blank_to!(j.min(n));
        } else if c == b'\'' {
            // A char literal, or a lifetime. `'"'` would otherwise flip string state.
            let lit_end = if i + 1 < n && b[i + 1] == b'\\' {
                // '\n' '\'' '\u{1F}'
                let mut j = i + 2;
                while j < n && b[j] != b'\'' {
                    j += 1;
                }
                if j < n { Some(j + 1) } else { None }
            } else if i + 2 < n && b[i + 2] == b'\'' {
                Some(i + 3)
            } else {
                None // lifetime
            };
            match lit_end {
                Some(j) => blank_to!(j.min(n)),
                None => {
                    out.push(c);
                    i += 1;
                }
            }
        } else {
            out.push(c);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap_or_else(|_| src.to_string())
}

fn prev_is_ident(b: &[u8], i: usize) -> bool {
    i > 0 && (b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_')
}

/// `Some(hashes)` when `b[i..]` opens a raw string (`r"`, `r#"`, `r##"`, ...).
fn raw_string_hashes(b: &[u8], i: usize) -> Option<usize> {
    let mut j = i + 1;
    while j < b.len() && b[j] == b'#' {
        j += 1;
    }
    if j < b.len() && b[j] == b'"' {
        Some(j - i - 1)
    } else {
        None
    }
}

fn find(b: &[u8], from: usize, needle: &[u8]) -> Option<usize> {
    if from >= b.len() {
        return None;
    }
    b[from..]
        .windows(needle.len())
        .position(|w| w == needle)
        .map(|p| p + from)
}

// ─────────────────────────────────────────────────────────────────────────────
// AUTHORING vs LOWERING
// ─────────────────────────────────────────────────────────────────────────────
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Site {
    /// The algebra ORIGINATES here — an authored constraint. Counted.
    Construct,
    /// The algebra ARRIVED here and is being read — a lowering / interpreter. Free.
    Pattern,
}

/// Index just past the delimiter group opened at `i`.
fn matching(b: &[u8], i: usize) -> usize {
    let mut depth = 0i32;
    let mut j = i;
    while j < b.len() {
        match b[j] {
            b'{' | b'(' | b'[' => depth += 1,
            b'}' | b')' | b']' => {
                depth -= 1;
                if depth == 0 {
                    return j + 1;
                }
            }
            _ => {}
        }
        j += 1;
    }
    b.len()
}

fn skip_ws(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && (b[i] as char).is_whitespace() {
        i += 1;
    }
    i
}

/// `name_end` points just past the `Type::Variant` path. Decide what it is.
fn classify_site(b: &[u8], path_start: usize, name_end: usize) -> Site {
    let n = b.len();
    let j = skip_ws(b, name_end);
    let after = if j < n && (b[j] == b'{' || b[j] == b'(') {
        let k = matching(b, j);
        let group = &b[j + 1..k.saturating_sub(1).max(j + 1)];
        // A bare `..` rest is pattern-only: a struct-update base must be `..expr`.
        let mut t = 0usize;
        while t + 1 < group.len() {
            if group[t] == b'.' && group[t + 1] == b'.' {
                let after_dots = skip_ws(group, t + 2);
                if after_dots >= group.len()
                    || matches!(group[after_dots], b',' | b'}' | b')' | b']')
                {
                    return Site::Pattern;
                }
            }
            t += 1;
        }
        k
    } else {
        j
    };
    // Patterns nest inside other patterns: `Some(LeanExpr::Const(v)) => ..`. Step out of
    // the enclosing pattern's parens/brackets before looking for the arm arrow. `}` is NOT
    // skipped — that would step out of a block and read the NEXT match arm's arrow.
    let mut j = skip_ws(b, after);
    while j < n && matches!(b[j], b')' | b']') {
        j = skip_ws(b, j + 1);
    }
    if j + 1 < n && b[j] == b'=' && b[j + 1] == b'>' {
        return Site::Pattern; // match arm
    }
    if j < n && b[j] == b'|' && !(j + 1 < n && b[j + 1] == b'|') {
        return Site::Pattern; // or-pattern
    }
    // `Variant { .. } if guard => ..`
    if j + 3 <= n && &b[j..j + 3] == b"if " {
        let end = (j + 300).min(n);
        let seg = &b[j..end];
        if let Some(p) = find(seg, 0, b"=>") {
            if !seg[..p].contains(&b';') {
                return Site::Pattern;
            }
        }
    }
    // Binding-position patterns: look back to the start of the statement.
    let stmt_start = b[..path_start]
        .iter()
        .rposition(|&c| c == b';' || c == b'{' || c == b'}')
        .map_or(0, |p| p + 1);
    let pre = &b[stmt_start..path_start];
    // `matches!(expr, PATTERN)` — only when the site is genuinely INSIDE the macro's
    // parens. A bare "there was a matches! earlier in this statement" test would
    // misclassify `matches!(a, X::Y{..}) && v.contains(&LeanExpr::Var(3))` as lowering.
    {
        let mut m = 0usize;
        while let Some(p) = find(b, m, b"matches!(") {
            if p >= path_start {
                break;
            }
            let open = p + b"matches!".len();
            if matching(b, open) > path_start {
                return Site::Pattern;
            }
            m = p + 1;
        }
    }
    let binder = find(pre, 0, b"if let ").is_some()
        || find(pre, 0, b"while let ").is_some()
        || find(pre, 0, b"let ").is_some();
    if binder && j < n && b[j] == b'=' && !(j + 1 < n && b[j + 1] == b'=') {
        return Site::Pattern; // `if let X::Y { .. } = expr` / `let X::Y(v) = expr else`
    }
    Site::Construct
}

// ─────────────────────────────────────────────────────────────────────────────
// The five dialects
// ─────────────────────────────────────────────────────────────────────────────

/// Dialects (3) and (4): the constraint IR types whose CONSTRUCTION is authored algebra.
const IR_TYPES: &[&str] = &[
    "ConstraintExpr",
    "LeanExpr",
    "VmConstraint2",
    "VmConstraint",
];

/// Cheap prefilter. A file with none of these cannot hold any dialect, so the ~2500-file
/// walk does not pay for a full lex. Exact given that `assert_eq`/`when` are only counted
/// inside an `AirBuilder` file.
const MARKERS: &[&str] = &[
    "assert_zero",
    "AirBuilder",
    "ConstraintExpr",
    "LeanExpr",
    "VmConstraint",
    "eval: Box::new",
];

#[derive(Default, Debug, Clone, Copy)]
struct Counts {
    /// (1) plonky3 symbolic builder calls.
    symbolic: usize,
    /// (2) closure constraints.
    closures: usize,
    /// (3)+(4) constraint-IR values CONSTRUCTED.
    ir_constructed: usize,
    /// (3)+(4) constraint-IR values DESTRUCTURED. Reported, never counted as a violation.
    ir_lowered: usize,
    /// How many of the AUTHORED sites sit inside a `#[cfg(test)]` item — a SUBSET of
    /// `authored()`, not a deduction from it. Reported so a failure message can say
    /// "8 of 8 are test-only" instead of leaving the reader to open the file.
    cfg_test: usize,
}

impl Counts {
    fn authored(&self) -> usize {
        self.symbolic + self.closures + self.ir_constructed
    }

    /// The `, N of them #[cfg(test)]-only` clause, or nothing when N is 0.
    fn cfg_test_note(&self) -> String {
        if self.cfg_test == 0 {
            String::new()
        } else if self.cfg_test == self.authored() {
            format!(", ALL {} inside `#[cfg(test)]`", self.cfg_test)
        } else {
            format!(", {} of them inside `#[cfg(test)]`", self.cfg_test)
        }
    }
}

fn ident_at(b: &[u8], i: usize) -> usize {
    let mut j = i;
    while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
        j += 1;
    }
    j
}

/// `.name(` with arbitrary whitespace around the dot (chained builders wrap lines), and
/// NOT `..name(`. A leading dot is what separates the `assert_eq` METHOD from the
/// `assert_eq!` macro. Returns the OFFSET of each hit so it can be attributed to a
/// `#[cfg(test)]` region (see `cfg_test_regions`) — the count alone cannot be.
fn method_call_sites(b: &[u8], names: &[&str], prefix_match: bool) -> Vec<usize> {
    let n = b.len();
    let mut hits = Vec::new();
    let mut i = 0usize;
    while i < n {
        if !(b[i].is_ascii_alphabetic() || b[i] == b'_') || prev_is_ident(b, i) {
            i += 1;
            continue;
        }
        let end = ident_at(b, i);
        let word = &b[i..end];
        let matched = names.iter().any(|nm| {
            let nb = nm.as_bytes();
            if prefix_match {
                word.starts_with(nb)
            } else {
                word == nb
            }
        });
        if matched {
            // preceding non-ws must be a single `.`
            let mut p = i;
            while p > 0 && (b[p - 1] as char).is_whitespace() {
                p -= 1;
            }
            let dotted = p > 0 && b[p - 1] == b'.' && !(p > 1 && b[p - 2] == b'.');
            let q = skip_ws(b, end);
            if dotted && q < n && b[q] == b'(' {
                hits.push(i);
            }
        }
        i = end.max(i + 1);
    }
    hits
}

/// Byte ranges of `#[cfg(test)]`-gated items. Computed on the BLANKED code, so a
/// commented-out attribute never opens a region.
///
/// ⚑ **This is ATTRIBUTION, not an exemption.** A site inside one of these ranges is
/// counted by `authored()` exactly like any other; the range only lets the failure
/// message say *which* sites are test-only, so the reader is not left guessing. See the
/// module docs' `#[cfg(test)]`-inside-`src/` note for why the counting stays strict.
///
/// Only the LITERAL `#[cfg(test)]` opens a range. `#[cfg(any(test, feature = "x"))]`
/// deliberately does not — that item compiles in a production build whenever the feature
/// is on, so calling it test-only would be false.
fn cfg_test_regions(b: &[u8]) -> Vec<(usize, usize)> {
    let n = b.len();
    // `#![cfg(test)]` is an INNER attribute: it gates the whole file.
    if find(b, 0, b"#![cfg(test)]").is_some() {
        return vec![(0, n)];
    }
    let attr = b"#[cfg(test)]";
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(p) = find(b, i, attr) {
        i = p + 1;
        let mut j = skip_ws(b, p + attr.len());
        // Any further outer attributes on the same item.
        while j < n && b[j] == b'#' {
            let Some(open) = find(b, j, b"[") else { break };
            j = skip_ws(b, matching(b, open));
        }
        // Visibility / qualifier words, then the item keyword.
        let mut item_has_body = true;
        loop {
            let e = ident_at(b, j);
            if e == j {
                break;
            }
            match std::str::from_utf8(&b[j..e]).unwrap_or("") {
                "pub" | "unsafe" | "async" | "default" => {
                    let k = skip_ws(b, e);
                    // `pub(crate)` / `pub(super)`
                    j = if b.get(k) == Some(&b'(') {
                        skip_ws(b, matching(b, k))
                    } else {
                        k
                    };
                }
                // Bodyless items: `use a::{b, c};` opens a brace that is NOT a region.
                "use" | "type" | "const" | "static" | "let" | "extern" => {
                    item_has_body = false;
                    break;
                }
                _ => break, // mod / fn / impl / struct / enum / trait / macro_rules
            }
        }
        if !item_has_body {
            continue;
        }
        // The body is the first brace group — but only if a `{` precedes the item's `;`.
        let mut k = j;
        while k < n && b[k] != b'{' && b[k] != b';' {
            k += 1;
        }
        if k < n && b[k] == b'{' {
            out.push((j, matching(b, k)));
        }
    }
    out
}

fn count_sites(raw: &str) -> Counts {
    count_sites_explained(raw, None)
}

/// `explain` collects `(line, "Type::Variant", Site)` so a maintainer can audit WHY a file
/// scores what it scores:
/// `LAW1_EXPLAIN=circuit/src/foo.rs cargo test -p dregg-circuit-prove --test law1_enforcement_gate -- --nocapture`
fn count_sites_explained(
    raw: &str,
    mut explain: Option<&mut Vec<(usize, String, Site)>>,
) -> Counts {
    let code = blank_noncode(raw);
    let b = code.as_bytes();
    let mut c = Counts::default();
    let regions = cfg_test_regions(b);
    let in_cfg_test = |p: usize| regions.iter().any(|&(s, e)| p >= s && p < e);

    // (1) `x.assert_zero(..)` on any receiver — this is the form the previous revision
    // missed on `b.assert_zero(&Head::..)`, which is param-compose's ENTIRE AIR.
    let mut sym = method_call_sites(b, &["assert_zero"], false);
    // `.assert_eq(..)` / `.when*(..)` are a constraint dialect only on an AirBuilder.
    if code.contains("AirBuilder") {
        sym.extend(method_call_sites(b, &["assert_eq"], false));
        sym.extend(method_call_sites(b, &["when"], true));
    }
    c.symbolic += sym.len();
    c.cfg_test += sym.iter().filter(|&&p| in_cfg_test(p)).count();

    // (2) closures.
    {
        let mut i = 0usize;
        while let Some(p) = find(b, i, b"eval") {
            let q = skip_ws(b, p + 4);
            if q < b.len() && b[q] == b':' && !prev_is_ident(b, p) {
                let r = skip_ws(b, q + 1);
                if b[r..].starts_with(b"Box::new") {
                    c.closures += 1;
                    if in_cfg_test(p) {
                        c.cfg_test += 1;
                    }
                }
            }
            i = p + 4;
        }
    }

    // (3)+(4) constraint IR: construction is authored, destructuring is not.
    let mut i = 0usize;
    while i < b.len() {
        if !(b[i].is_ascii_alphabetic() || b[i] == b'_') || prev_is_ident(b, i) {
            i += 1;
            continue;
        }
        let end = ident_at(b, i);
        let word = std::str::from_utf8(&b[i..end]).unwrap_or("");
        if IR_TYPES.contains(&word) && b[end..].starts_with(b"::") {
            let vstart = end + 2;
            let vend = ident_at(b, vstart);
            if vend > vstart && b[vstart].is_ascii_uppercase() {
                let site = classify_site(b, i, vend);
                match site {
                    Site::Construct => {
                        c.ir_constructed += 1;
                        if in_cfg_test(i) {
                            c.cfg_test += 1;
                        }
                    }
                    Site::Pattern => c.ir_lowered += 1,
                }
                if let Some(ex) = explain.as_deref_mut() {
                    let line = b[..i].iter().filter(|&&x| x == b'\n').count() + 1;
                    ex.push((
                        line,
                        String::from_utf8_lossy(&b[i..vend]).into_owned(),
                        site,
                    ));
                }
                i = vend;
                continue;
            }
        }
        i = end.max(i + 1);
    }
    c
}

// ─────────────────────────────────────────────────────────────────────────────
// Scope: every `src/` tree in the repository.
// ─────────────────────────────────────────────────────────────────────────────
/// Directories that hold no compiled first-party Rust, or hold the place the algebra is
/// SUPPOSED to live. Keep this list boring and justifiable — it is the one place a
/// violation could be parked deliberately.
const SKIP_DIRS: &[&str] = &[
    "target", // build output
    ".git",
    "node_modules",
    "vendor", // third-party forks (bulletproofs-r1cs-wgpu, curve25519-dalek-dregg)
    "docs",   // prose + byte-copies of Rust kept as documentation artifacts
    ".cache",
    ".lake",
    "metatheory", // Lean. This is WHERE ALGEBRA BELONGS.
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("circuit-prove has a parent")
        .to_path_buf()
}

fn scan_repo() -> BTreeMap<String, Counts> {
    scan_tree(&repo_root())
}

/// Parameterised on the root so the RED path (`teeth::the_gate_goes_red_on_a_hand_written_air`)
/// exercises this exact walker over a synthetic tree instead of a reimplementation of it.
fn scan_tree(root: &Path) -> BTreeMap<String, Counts> {
    let mut found = BTreeMap::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            if p.is_dir() {
                if SKIP_DIRS.contains(&name.as_str()) || name.starts_with('.') {
                    continue;
                }
                stack.push(p);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let rel = p
                .strip_prefix(root)
                .unwrap_or(&p)
                .to_string_lossy()
                .replace('\\', "/");
            // Only compiled crate sources. `tests/` trees are a NAMED blind spot (module docs).
            if !rel.contains("/src/") {
                continue;
            }
            let Ok(raw) = std::fs::read_to_string(&p) else {
                continue;
            };
            if !MARKERS.iter().any(|m| raw.contains(m)) {
                continue;
            }
            let c = count_sites(&raw);
            if c.authored() > 0 {
                found.insert(rel, c);
            }
        }
    }
    found
}

// ─────────────────────────────────────────────────────────────────────────────
// The ratchet. Frozen ground truth as re-measured 2026-07-25 with the widened scope,
// the fifth `assert_zero` form, the descriptor-tree dialect, and patterns no longer
// miscounted. 88 files, 1560 authored sites (494 further sites are lowering/destructuring
// and are FREE). Every entry is debt that is ALLOWED to shrink and MUST NOT grow.
//
// This was measured on a tree with several sibling lanes committing into `circuit/src` during
// the same hour, so a GREW line the day after this lands is as likely to be honest churn from
// that work as a fresh violation — read the file, then either fix it or re-print the ledger.
// ─────────────────────────────────────────────────────────────────────────────
#[rustfmt::skip]
const BASELINE: &[(&str, usize)] = &[
    ("circuit-prove/src/bridge_leaf_adapter.rs", 3),
    ("circuit-prove/src/carrier_pin_twin.rs", 6),
    ("circuit-prove/src/caveat_admission_leaf_adapter.rs", 32),
    ("circuit-prove/src/custom_leaf_adapter.rs", 3),
    ("circuit-prove/src/deco_leaf_adapter.rs", 21),
    // ⚑ THE CRATE'S ONE TEST-ONLY TOY AIR lives here, and all 8 sites are it:
    // `toy_fib_air::ToyFibAir`, the p3 uni-stark 2-column Fibonacci, `#[cfg(test)]`-gated,
    // shared by `dregg_outer_config`, `gpu_backend` and `dregg_mina_config`. It constrains
    // nothing about dregg state — a StarkConfig round-trip needs *an* AIR and it must
    // deliberately not be a real one. This row is the price of that, paid ONCE.
    ("circuit-prove/src/dregg_outer_config.rs", 8),
    ("circuit-prove/src/dsl_leaf_adapter.rs", 3),
    ("circuit-prove/src/effect_vm_p3_air.rs", 11),
    ("circuit-prove/src/factory_leaf_adapter.rs", 5),
    // ── `circuit-prove/src/gpu_backend.rs` (was 8) is GONE from this ledger, 2026-07-30.
    //    Its 8 sites were a second private copy of the toy Fibonacci AIR above; the copy is
    //    deleted and `gpu_backend::tests` imports `toy_fib_air` instead, so the file now
    //    authors ZERO. The row is REMOVED rather than left at 8, because 8 sites of unused
    //    slack in a ratchet is 8 hand-authored constraints a later lane can add without the
    //    gate noticing (the same reason `descriptor_ir2.rs` was re-pinned 298 -> 283).
    //    A byproduct worth naming: the GPU/CPU byte-identity test now proves literally the
    //    same `Air` impl under both configs, so a byte difference cannot be the AIR's.
    ("circuit-prove/src/hatchery_leaf_adapter.rs", 5),
    ("circuit-prove/src/joint_turn_recursive.rs", 28),
    ("circuit-prove/src/lean_lookup_air.rs", 3),
    ("circuit-prove/src/membership_leaf_adapter.rs", 3),
    ("circuit-prove/src/mpt_holding_leaf.rs", 8),
    ("circuit-prove/src/note_spend_leaf_adapter.rs", 41),
    ("circuit-prove/src/private_book_bfv_terminal/fused.rs", 24),
    ("circuit-prove/src/private_graph_rewrite_cell.rs", 2),
    ("circuit-prove/src/private_preference_cell.rs", 2),
    ("circuit-prove/src/shielded/attest.rs", 11),
    ("circuit-prove/src/shielded/spend_circuit.rs", 11),
    // circuit-prove/src/shielded/wide_value_binding.rs is GONE from this ledger (was 7).
    // Dregg2/Circuit/Emit/WideValueBindingEmit.lean authors the whole AIR (byte-pinned, 29874 B)
    // and WideValueBindingRefine proves EVERY emitted constraint — including
    // legacy_join_cannot_separate_aliases, which needs no crypto: the one-felt legacy join is
    // provably blind to a v / v+p alias pair, for ANY hash. The sidecar now reads that golden
    // and proves through Plonky3HidingFriReference (the SAME create_zk_config the retired
    // prove_dsl_zk route used, so hiding is preserved); the descriptor-authoring half of the
    // file — mod col's AIR use, constant_gate, limb_recompose, u64_recompose,
    // wide_input_columns, wide_value_binding_descriptor, wide_value_binding_circuit — is deleted.
    ("circuit-prove/src/shielded_ring_clearing_air.rs", 75),
    ("circuit-prove/src/shielded_ring_clearing_nleg_air.rs", 32),
    ("circuit-prove/src/shielded_spend_leaf_adapter.rs", 39),
    ("circuit-prove/src/solvency_leaf_adapter.rs", 27),
    ("circuit-prove/src/sovereign_leaf_adapter.rs", 3),
    ("circuit-prove/src/zkoracle_leaf_adapter.rs", 16),
    ("circuit/src/bilateral_aggregation_air.rs", 16),
    ("circuit/src/blinded_membership_witness.rs", 5),
    ("circuit/src/bound_presentation_witness.rs", 1),
    ("circuit/src/committed_threshold.rs", 7),
    ("circuit/src/constraint_prover.rs", 1),
    ("circuit/src/custom_leaf_lowering.rs", 64),
    ("circuit/src/delegate_descriptor.rs", 2),
    ("circuit/src/derivation_air.rs", 1),
    ("circuit/src/descriptor_by_name.rs", 1),
    // TIGHTENED 2026-07-30, 298 -> 283. `Ir2Air::Main`'s four grouped constraint blocks
    // (when_first_row / when_last_row / when_transition / every-row) collapsed into ONE shared
    // `eval_row_local_constraints` walk with a single `assert_zero`, which `Ir2UniAir` also calls
    // — so the row-local algebra now has exactly one interpreter instead of two. The row is
    // re-pinned to the measurement rather than left at its old allowance: 15 sites of unused slack
    // in a ratchet is 15 hand-authored constraints a later lane can add without the gate noticing.
    ("circuit/src/descriptor_ir2.rs", 283),
    ("circuit/src/descriptor_ir2_canonical.rs", 48),
    ("circuit/src/direct_logic_frontend.rs", 3),
    ("circuit/src/dsl/accumulator.rs", 10),
    ("circuit/src/dsl/cap_membership.rs", 4),
    ("circuit/src/dsl/committed_threshold.rs", 7),
    ("circuit/src/dsl/derivation.rs", 58),
    ("circuit/src/dsl/descriptors.rs", 7),
    ("circuit/src/dsl/dfa_routing.rs", 9),
    ("circuit/src/dsl/dsl_p3_air.rs", 25),
    ("circuit/src/dsl/fold.rs", 15),
    ("circuit/src/dsl/garbled.rs", 14),
    ("circuit/src/dsl/note_spending.rs", 23),
    ("circuit/src/dsl/openable_fields_insertion.rs", 6),
    ("circuit/src/dsl/predicates/arithmetic.rs", 42),
    ("circuit/src/dsl/predicates/base.rs", 34),
    ("circuit/src/dsl/predicates/compound.rs", 20),
    ("circuit/src/dsl/predicates/relational.rs", 31),
    ("circuit/src/dsl/temporal_absence.rs", 4),
    ("circuit/src/effect_action_air.rs", 3),
    ("circuit/src/effect_vm/authority_digest_weld.rs", 11),
    ("circuit/src/effect_vm/bare_floor_refuse_weld.rs", 11),
    ("circuit/src/effect_vm/burn_avail_weld.rs", 1),
    ("circuit/src/effect_vm/carrier_floor_weld.rs", 11),
    ("circuit/src/effect_vm/discharge_weld.rs", 5),
    ("circuit/src/effect_vm/satisfaction_weld.rs", 2),
    ("circuit/src/effect_vm/transfer_avail_weld.rs", 1),
    ("circuit/src/effect_vm/transfer_fee_avail_weld.rs", 1),
    ("circuit/src/effect_vm/vault_weld.rs", 5),
    ("circuit/src/effect_vm_descriptors.rs", 18),
    ("circuit/src/lean_descriptor_air.rs", 47),
    ("circuit/src/membership_descriptor_4ary.rs", 1),
    ("circuit/src/membership_descriptor_general.rs", 39),
    ("circuit/src/merkle_types.rs", 4),
    ("circuit/src/note_spend_witness.rs", 41),
    ("circuit/src/plonky3_prover.rs", 7),
    ("circuit/src/plonky3_recursion.rs", 6),
    ("circuit/src/presentation.rs", 1),
    ("circuit/src/whole_image_fold.rs", 38),
    // ── OUTSIDE the old two-directory scope: the surface this gate could not see ──
    ("constraint-lowering/src/lib.rs", 8),
    ("dregg-doc/src/ci_assurance.rs", 1),
    ("dregg-dsl-differential/src/plonky3_runner.rs", 10),
    ("dregg-dsl-runtime/src/composition.rs", 13),
    ("game-turn-slice/src/compiler.rs", 6),
    // ── THE LAW WON HERE (2026-07-25). `param-compose/src/air.rs` (19 sites) and
    //    `param-compose/src/builder.rs` (9) — the largest hand-written Rust AIR in the tree,
    //    1028 lines — are DELETED. Dregg2/Circuit/Emit/ParamComposeEmit.lean authors the whole
    //    AIR and byte-pins the wire, all 18 shapes the corpus exercises are #guard-pinned, and
    //    param-compose's own test corpus now rides the emitted descriptor. Their rows are gone
    //    from this BASELINE in that same change (the stale-entry check below requires it).
    ("perf/src/lib.rs", 28),  // ⚑ a hand-built VmConstraint2::{MapOp,UMemOp} descriptor.
    ("sdk/src/full_turn_proof.rs", 2),
    ("tests/src/dsl_pipeline.rs", 8),
    ("turn/src/executor/membership_verifier.rs", 2),
    ("turn/src/umem.rs", 8),
];

/// Dialect (5). The law names `air_accepts` predicates explicitly, so they are ledgered by
/// name with a reason rather than folded into a count. A NEW one fails.
#[rustfmt::skip]
const AIR_ACCEPTS_LEDGER: &[(&str, &str)] = &[
    ("circuit/src/lean_descriptor_air.rs",
     "test-module ORACLE: it does not decide acceptance itself, it calls prove_vm_descriptor + \
      verify_vm_descriptor and treats a prover panic as reject. Delegation, not authorship."),
    // `param-compose/src/builder.rs`'s `air_accepts` — a real hand-authored acceptance predicate
    // over a hand-authored Rust AIR, paired with tamper() for forgery tests — is DELETED with the
    // AIR (2026-07-25), so it needs no ledger line. It was retired exactly as this ledger demanded:
    // with the AIR, not separately.
    // `entity-compose/src/lib.rs` — RETIRED 2026-07-25. Its line claimed the crate "rebuilds the
    // param-compose AIR and calls ITS air_accepts". Both halves are now false: entity-compose defines
    // no `air_accepts` at all, and it references neither `param_compose::air` nor `::builder` — it
    // proves the Lean-emitted descriptor directly. The line survived a lane's deletion because THIS
    // LEDGER HAD NO STALE-CHECK: the test below only hunted NEW entries, so a row describing an
    // object that no longer exists passed green while lying. That check now exists (see
    // `stale` in `law1_no_new_rust_authored_air_accepts`), which is why this row could be removed
    // instead of quietly rotting.
];

fn print_baseline(found: &BTreeMap<String, Counts>) {
    println!("// LAW1 baseline, machine-printed:");
    for (f, c) in found {
        let note = if c.cfg_test > 0 {
            format!("  // {} of {} #[cfg(test)]", c.cfg_test, c.authored())
        } else {
            String::new()
        };
        println!("    (\"{f}\", {}),{note}", c.authored());
    }
    println!(
        "// {} files, {} authored sites ({} of them inside #[cfg(test)], counted all the same), \
         {} lowering sites (free)",
        found.len(),
        found.values().map(|c| c.authored()).sum::<usize>(),
        found.values().map(|c| c.cfg_test).sum::<usize>(),
        found.values().map(|c| c.ir_lowered).sum::<usize>(),
    );
}

/// The ratchet itself: a NEW file fails, a listed file that GREW fails, shrinking is always
/// allowed (that is the direction of the law), and a ledger line for a file that no longer
/// exists fails so the debt cannot be inflated by rot. Parameterised so the teeth below run
/// THIS code against a synthetic tree.
fn ratchet(
    root: &Path,
    found: &BTreeMap<String, Counts>,
    baseline: &[(&str, usize)],
) -> Vec<String> {
    let base: BTreeMap<&str, usize> = baseline.iter().map(|(f, n)| (*f, *n)).collect();
    let mut violations = Vec::new();
    for (rel, c) in found {
        let n = c.authored();
        match base.get(rel.as_str()) {
            None => violations.push(format!(
                "  NEW Rust-authored constraints: {rel} ({n} sites: {} symbolic, {} closure, {} IR{})\n\
                      -> EMIT IT FROM LEAN. Do not add it to the baseline.\n\
                      -> If the sites are `#[cfg(test)]`-only they are STILL a hand-written Rust AIR, and the\n\
                         remedy is still not a baseline row: reuse the crate's one shared test AIR\n\
                         (`circuit-prove/src/dregg_outer_config.rs::toy_fib_air`) or delete the copy.",
                c.symbolic, c.closures, c.ir_constructed, c.cfg_test_note()
            )),
            Some(allowed) if n > *allowed => violations.push(format!(
                "  GREW: {rel} ({allowed} -> {n} sites)\n\
                      -> new hand-authored constraints. Emit them from Lean."
            )),
            _ => {}
        }
    }
    for (f, n) in baseline {
        if !root.join(f).exists() {
            violations.push(format!(
                "  STALE BASELINE ENTRY: {f} ({n} sites) no longer exists.\n\
                      -> the law WON here. Delete this line from BASELINE."
            ));
        }
    }
    violations
}

#[test]
fn law1_no_new_rust_authored_constraints() {
    if let Ok(f) = std::env::var("LAW1_EXPLAIN") {
        let raw = std::fs::read_to_string(repo_root().join(&f)).expect("LAW1_EXPLAIN path");
        let mut ex = Vec::new();
        let c = count_sites_explained(&raw, Some(&mut ex));
        println!("{f}: {c:?}");
        for (line, what, site) in ex {
            println!(
                "  {:>6}  {}  {what}",
                line,
                if site == Site::Construct {
                    "AUTHORED "
                } else {
                    "lowering "
                }
            );
        }
    }
    let found = scan_repo();
    if std::env::var("LAW1_PRINT_BASELINE").is_ok() {
        print_baseline(&found);
    }
    let violations = ratchet(&repo_root(), &found, BASELINE);
    assert!(
        violations.is_empty(),
        "\n\nARCHITECTURAL LAW #1 VIOLATED — Rust must author NO constraints.\n\n{}\n\n\
         See this file's module docs for how to emit from Lean instead. Re-print the ledger with\n\
         LAW1_PRINT_BASELINE=1 cargo test -p dregg-circuit-prove --test law1_enforcement_gate -- --nocapture\n",
        violations.join("\n")
    );
}

/// `fn air_accepts` / `fn <something>_air_accepts` — a DEFINITION, not a call site and not
/// a test named after one (`fn air_accepts_valid_ring3` is a test, and does not count).
fn defines_air_accepts(code: &str) -> bool {
    let b = code.as_bytes();
    let mut i = 0usize;
    while let Some(p) = find(b, i, b"fn ") {
        if !prev_is_ident(b, p) {
            let s = skip_ws(b, p + 3);
            let e = ident_at(b, s);
            let name = std::str::from_utf8(&b[s..e]).unwrap_or("");
            if name == "air_accepts" || name.ends_with("_air_accepts") {
                return true;
            }
        }
        i = p + 3;
    }
    false
}

#[test]
fn law1_no_new_rust_authored_air_accepts() {
    let root = repo_root();
    let ledgered: Vec<&str> = AIR_ACCEPTS_LEDGER.iter().map(|(f, _)| *f).collect();
    let mut new_ones = Vec::new();
    for rel in scan_repo_all_src() {
        let Ok(raw) = std::fs::read_to_string(root.join(&rel)) else {
            continue;
        };
        if !raw.contains("air_accepts") || !defines_air_accepts(&blank_noncode(&raw)) {
            continue;
        }
        if !ledgered.contains(&rel.as_str()) {
            new_ones.push(rel);
        }
    }
    assert!(
        new_ones.is_empty(),
        "\n\nARCHITECTURAL LAW #1 VIOLATED — a Rust-authored `air_accepts` predicate.\n{}\n\n\
         The law names these explicitly: acceptance is decided by the EMITTED artifact and the prover,\n\
         never by a Rust function that re-implements the AIR. If a new one is genuinely a delegating\n\
         oracle, add it to AIR_ACCEPTS_LEDGER *with the reason*.\n",
        new_ones.join("\n")
    );

    // STALE-ENTRY CHECK. Without this the ledger passes green while LYING: a row survives the file
    // it describes, and the debt it records reads as live when the object is gone. That happened —
    // `entity-compose/src/lib.rs` sat here after the crate stopped defining `air_accepts` at all.
    // A ledger that cannot go red about its own rot is not a ledger.
    let stale: Vec<&str> = AIR_ACCEPTS_LEDGER
        .iter()
        .map(|(f, _)| *f)
        .filter(|rel| {
            match std::fs::read_to_string(root.join(rel)) {
                Ok(raw) => !defines_air_accepts(&blank_noncode(&raw)),
                Err(_) => true, // the file itself is gone
            }
        })
        .collect();
    assert!(
        stale.is_empty(),
        "\n\nSTALE AIR_ACCEPTS_LEDGER ENTRY — the law WON here, the ledger just did not notice.\n{}\n\n\
         Each listed file no longer defines `air_accepts` (or no longer exists), so its ledger line\n\
         describes an object that is not there and overstates the remaining debt. Delete the line.\n",
        stale.join("\n")
    );
}

/// Every `.rs` under a `src/` tree in scope, without the marker prefilter (the `air_accepts`
/// check has a different trigger word).
fn scan_repo_all_src() -> Vec<String> {
    let root = repo_root();
    let mut out = Vec::new();
    let mut stack = vec![root.clone()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            if p.is_dir() {
                if SKIP_DIRS.contains(&name.as_str()) || name.starts_with('.') {
                    continue;
                }
                stack.push(p);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let rel = p
                .strip_prefix(&root)
                .unwrap_or(&p)
                .to_string_lossy()
                .replace('\\', "/");
            if rel.contains("/src/") {
                out.push(rel);
            }
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The gate's own teeth. A gate that cannot go red is not a gate — and a gate whose
// CLASSIFIER is wrong goes red on the wrong things, which is how the previous revision
// accumulated 46 phantom violations in one lowering. These fixtures pin both directions.
// ─────────────────────────────────────────────────────────────────────────────
mod teeth {
    use super::*;

    #[test]
    fn destructuring_is_not_authoring() {
        // Every shape the LOWERINGS actually use. None of these author algebra.
        let lowering = r#"
            fn gate_body(e: &ConstraintExpr) -> LeanExpr {
                match e {
                    ConstraintExpr::Equality { col_a, col_b } => zero(),
                    ConstraintExpr::Binary { .. } => zero(),
                    ConstraintExpr::Gated { .. } if flag => zero(),
                    ConstraintExpr::Hash { .. } | ConstraintExpr::Hash2to1 { .. } => zero(),
                    _ => zero(),
                }
            }
            fn n(c: &ConstraintExpr) -> bool { matches!(c, ConstraintExpr::MerkleHash8 { .. }) }
            fn m(c: &ConstraintExpr) { if let ConstraintExpr::Squared { inner } = c { drop(inner) } }
        "#;
        let c = count_sites(lowering);
        assert_eq!(c.ir_constructed, 0, "a lowering authored nothing: {c:?}");
        assert_eq!(c.ir_lowered, 7, "all seven sites are destructuring: {c:?}");
    }

    #[test]
    fn construction_is_authoring() {
        let authored = r#"
            fn build() -> Vec<ConstraintExpr> {
                vec![
                    ConstraintExpr::Binary { col: 3 },
                    ConstraintExpr::Polynomial { terms: t },
                    ConstraintExpr::Gated { gate: g, ..base },
                ]
            }
            fn tree() -> VmConstraint2 {
                VmConstraint2::Base(VmConstraint::PiBinding { row: VmRow::First, col: 0, pi: 1 })
            }
            fn leaf() -> LeanExpr { LeanExpr::mul(LeanExpr::Var(2), LeanExpr::Const(1)) }
        "#;
        let c = count_sites(authored);
        assert_eq!(c.ir_constructed, 7, "seven constructed IR values: {c:?}");
        assert_eq!(c.ir_lowered, 0, "nothing destructured: {c:?}");
    }

    #[test]
    fn the_fifth_assert_zero_dialect_is_visible() {
        // param-compose's actual form. The previous revision hard-coded `builder.` and saw ZERO.
        let param_compose_shaped = r#"
            fn build(b: &mut Builder) {
                b.assert_zero(&Head::lin(1, col).add_const(-1));
                b
                    .assert_zero(&Head::lin(-1, out).add_prod(1, vec![a, b]));
                self.assert_zero(&recomp);
            }
        "#;
        let c = count_sites(param_compose_shaped);
        assert_eq!(
            c.symbolic, 3,
            "three assert_zero sites on non-`builder` receivers: {c:?}"
        );
    }

    #[test]
    fn gpui_when_is_not_a_constraint() {
        // starbridge-v2's cockpit is full of `.when(cond, |el| ..)`. Without the AirBuilder
        // guard, widening the scope to the workspace would have invented hundreds of violations.
        let gpui =
            r#"fn ui(el: Div) -> Div { el.when(flag, |e| e.child(x)).when_some(o, |e, v| e) }"#;
        assert_eq!(count_sites(gpui).symbolic, 0);
        let air = r#"fn eval<AB: AirBuilder>(b: &mut AB) { b.when_transition().assert_eq(a, c); }"#;
        assert_eq!(
            count_sites(air).symbolic,
            2,
            "when_transition + assert_eq inside an AirBuilder"
        );
    }

    /// `#[cfg(test)]` ATTRIBUTES a site; it never forgives one. Both halves are pinned,
    /// because the tempting "fix" for the 2026-07-30 red was to subtract these from
    /// `authored()` — which would have made a copied Rust AIR in a `src/` file invisible
    /// exactly when the gate needed to see it.
    #[test]
    fn cfg_test_sites_are_counted_and_merely_attributed() {
        let mixed = r#"
            fn prod<AB: AirBuilder>(b: &mut AB) { b.assert_zero(x); }
            #[cfg(test)]
            mod tests {
                use p3_air::{Air, AirBuilder};
                fn toy<AB: AirBuilder>(b: &mut AB) {
                    b.assert_zero(y);
                    b.assert_eq(y, z);
                    b.push(ConstraintExpr::Binary { col: 3 });
                }
            }
        "#;
        let c = count_sites(mixed);
        assert_eq!(
            c.authored(),
            4,
            "cfg(test) sites are STILL counted as authored: {c:?}"
        );
        assert_eq!(c.cfg_test, 3, "three of the four are test-only: {c:?}");
        assert!(
            c.cfg_test_note().contains('3'),
            "the message names the split: {}",
            c.cfg_test_note()
        );

        // A `use a::{b, c};` under the attribute opens a brace that is NOT a body — if the
        // region walker took it, everything after the import would read as test-only.
        let prod_only = r#"fn f<AB: AirBuilder>(b: &mut AB) { b.assert_zero(x); }"#;
        assert_eq!(count_sites(prod_only).cfg_test, 0);
    }

    /// `#[cfg(any(test, feature = "x"))]` is NOT test-only: that item compiles into a
    /// production build whenever the feature is on. Only the literal `#[cfg(test)]` counts.
    #[test]
    fn cfg_any_test_feature_is_not_test_only() {
        let src = r#"
            #[cfg(any(test, feature = "probe"))]
            mod maybe {
                fn f<AB: AirBuilder>(b: &mut AB) { b.assert_zero(x); }
            }
        "#;
        let c = count_sites(src);
        assert_eq!(c.authored(), 1, "still authored: {c:?}");
        assert_eq!(
            c.cfg_test, 0,
            "a feature can turn this on in a shipped build: {c:?}"
        );
    }

    #[test]
    fn comments_and_strings_are_not_algebra() {
        let doc = r#"
            /// Lowers ConstraintExpr::Binary into LeanExpr::mul.
            // b.assert_zero(&Head::zero());
            fn f() -> &'static str { "ConstraintExpr::Polynomial" }
        "#;
        let c = count_sites(doc);
        assert_eq!(c.authored(), 0, "prose is not a constraint: {c:?}");
        assert_eq!(c.ir_lowered, 0);
    }

    /// END-TO-END RED PATH. A gate that cannot go red is not a gate — so this runs the REAL
    /// walker (`scan_tree`) and the REAL ratchet (`ratchet`) over a synthetic repo containing
    /// a hand-written Rust AIR, and asserts each failure mode fires. If someone neuters the
    /// scanner or the comparison, this goes red before the (green) production ledger can lie.
    #[test]
    fn the_gate_goes_red_on_a_hand_written_air() {
        let tmp = std::env::temp_dir().join(format!("law1-red-{}", std::process::id()));
        let src = tmp.join("evilcrate/src");
        std::fs::create_dir_all(&src).expect("tmp tree");
        std::fs::write(
            src.join("hand_written_air.rs"),
            "pub fn build(b: &mut Builder) {\n\
             \x20   b.assert_zero(&Head::lin(1, 0).add_const(-1));\n\
             \x20   b.push(ConstraintExpr::Binary { col: 4 });\n\
             \x20   b.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Var(2))));\n\
             }\n",
        )
        .expect("write evil");

        let found = scan_tree(&tmp);
        let key = "evilcrate/src/hand_written_air.rs";
        let counts = found.get(key).copied().unwrap_or_else(|| {
            panic!("the walker did not even SEE the hand-written AIR; found: {found:?}")
        });
        assert_eq!(counts.symbolic, 1, "the assert_zero dialect: {counts:?}");
        assert_eq!(
            counts.ir_constructed, 4,
            "ConstraintExpr + 3 gate-tree nodes: {counts:?}"
        );

        // 1. an UNLISTED file is a violation.
        let v = ratchet(&tmp, &found, &[]);
        assert!(
            v.iter()
                .any(|s| s.contains("NEW Rust-authored constraints") && s.contains(key)),
            "a new hand-written AIR must fail the gate; got {v:?}"
        );
        // 2. a listed file that GREW is a violation.
        let v = ratchet(&tmp, &found, &[(key, 4)]);
        assert!(
            v.iter().any(|s| s.contains("GREW") && s.contains(key)),
            "growth past the baseline must fail; got {v:?}"
        );
        // 3. at or below baseline is clean — shrinking is the direction of the law.
        assert!(
            ratchet(&tmp, &found, &[(key, 5)]).is_empty(),
            "at baseline: green"
        );
        assert!(
            ratchet(&tmp, &found, &[(key, 99)]).is_empty(),
            "shrunk: green"
        );
        // 4. a ledger line for a vanished file is a violation (debt must not rot upward).
        let v = ratchet(&tmp, &found, &[(key, 5), ("evilcrate/src/deleted.rs", 12)]);
        assert!(
            v.iter().any(|s| s.contains("STALE BASELINE ENTRY")),
            "a stale ledger line must fail; got {v:?}"
        );

        std::fs::remove_dir_all(&tmp).ok();
    }

    #[test]
    fn the_scope_reaches_outside_the_two_old_directories() {
        // The regression that made this rewrite necessary: the biggest Rust AIR in the tree
        // (`param-compose/src/{air,builder}.rs`) sat outside the scanned `circuit/src` +
        // `circuit-prove/src` and was invisible to a gate whose whole purpose was to see it.
        //
        // That AIR is now DELETED (2026-07-25) — so it can no longer serve as the scope probe,
        // and the probe moves to the OTHER files the two-directory scope hid. If this stops
        // finding them, the scope broke again.
        let found = scan_repo();
        for f in [
            "perf/src/lib.rs",
            "constraint-lowering/src/lib.rs",
            "dregg-dsl-runtime/src/composition.rs",
            "game-turn-slice/src/compiler.rs",
        ] {
            assert!(
                found.contains_key(f),
                "{f} authors constraints outside circuit/ + circuit-prove/ and the gate must \
                 see it; scope regressed"
            );
        }
        // ...and the file the probe used to be is GONE, which is the direction of the law. A
        // reappearance is a NEW hand-written Rust AIR and must not pass silently.
        for gone in ["param-compose/src/air.rs", "param-compose/src/builder.rs"] {
            assert!(
                !repo_root().join(gone).exists(),
                "{gone} was DELETED — a hand-written Rust AIR must not come back"
            );
        }
        assert!(
            found.len() > 60,
            "the widened scope should reach ~86 files across the workspace, found {}",
            found.len()
        );
    }
}
