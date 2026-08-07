//! **MOCK-PROOF PURGE RATCHET** — no production surface may ride a mock prover, ever again.
//!
//! ember, 2026-07-16: *"we need to get rid of all that mock shit… it gotta get purged. need to be wired
//! to real."* A mock proof/verify surface is the WORST lie this codebase can tell: it reports
//! `"valid"`/`"proved"` for data it never proved. This gate makes the purge PERMANENT — the baseline
//! below only ever SHRINKS.
//!
//! ## What counts as a mock prover (the engines, characterized from source — not from their comments)
//! * `circuit/src/ivc.rs` — WAS the SIMULATED IVC: `prove_ivc` built a hash-chain "proof";
//!   `verify_ivc` only recomputed a BLAKE3 digest over the proof's OWN public data.
//!   **Anyone who could call `prove_ivc` could mint a passing proof for any root walk.** Proof sizes
//!   were fabricated; `create_test_chain` fabricated the data itself. DELETED 2026-07-16 (final cut) —
//!   only the real Poseidon2 hash-chain primitives remain in that file.
//! * `circuit/src/constraint_prover.rs` — the row-by-row local checker. Says it of itself: a trace
//!   digest is *"**not** a cryptographic proof … nothing here is sound against a prover that lies"*;
//!   `generate_unchecked` skips even the local constraint check. 2026-07-17: renamed to honest
//!   VALIDATOR names (`ConstraintValidator` / `TraceSummary`; a "prover" that proves nothing was the
//!   `*_air`-on-a-non-AIR fiction). The 2026-07-17 consumer census found NOTHING treating its output
//!   as a proof: every production presentation verifier requires + cryptographically verifies the
//!   separate `real_stark_proof` descriptor wires, and the trace summaries riding
//!   `PresentationProof` are unread metadata. It survives as a legitimate prover-side/test validator.
//!
//! ## The REAL prover (the wiring target)
//! `circuit-prove/src/ivc_turn_chain.rs`: `prove_turn_chain_recursive(&[FinalizedTurn]) -> WholeChainProof`
//! (:1714), verified by `verify_whole_chain_proof_bytes` (:1598) — consumed for real by
//! `lightclient/src/lib.rs`. Per-effect proving is `descriptor_by_name` + `prove_vm_descriptor2`.
//! `preflight/src/checks/derivation_descriptor.rs` is the IN-REPO TEMPLATE for a correct migration
//! (real `prove_vm_descriptor2`/`verify_vm_descriptor2`; it explicitly REFUSES the trace-digest path).
//!
//! ## Why some entries are not one-line swaps (read before "just wiring" one)
//! A `FinalizedTurn` wraps a `DescriptorParticipant` — the rotated turn descriptor, produced at PROVING
//! time. A `TurnReceipt` (what `cclerk.receipt_chain()` retains) is HASHES ONLY. So a mock may exist
//! because the provable data was **discarded at that layer**; wiring real then needs RETENTION/plumbing,
//! not a swap. The plumbing already exists but is uncalled in production:
//! `turn/src/rotation_witness.rs:731 finalized_turn_from_full_turn` re-proves the rotated leg and
//! FAIL-CLOSES unless the leg's anchors equal the served `FullTurnProof`'s proven commits — its context
//! exists exactly once, at `node/src/blocklace_sync.rs::execute_finalized_turn` (:4287), which today
//! persists only the `FullTurnProof`. Persist the `FinalizedTurn` there and the chain becomes provable.
//!
//! ## How it counts (2026-08-07 — read this before believing a verdict)
//! It counts **Rust identifiers in code**, not text. Comments are blanked and a match must
//! sit on identifier boundaries — see `blank_comments`, which carries the two FALSE REDS
//! that the previous raw `src.matches(p)` substring scan produced at HEAD and the falsifiers
//! that now hold it to it. If you change the counter, those falsifiers are the gate on the
//! gate; do not weaken them.
//!
//! ## If this test fails
//! You added a production surface that rides a mock prover. **Do NOT add yourself to the baseline.**
//! Wire it to the real prover above. If the provable data is not at your layer, FAIL CLOSED (return an
//! honest error — `node/src/mcp/handlers_verify.rs::tool_prove_sovereign_turn` :206-212 is the honest
//! pattern) and name the plumbing. A mock that answers "valid" is never acceptable.

use std::path::Path;

/// The mock-prover surface, named as Rust identifiers.
///
/// A trailing `(` means "the CALL", so a same-named type/field does not count.
const MOCK_PATTERNS: &[&str] = &[
    "prove_ivc(",
    "verify_ivc(",
    "create_test_chain(",
    "ConstraintProof",
    // 2026-07-17: `ConstraintProof` was renamed `TraceSummary` (and
    // `ConstraintProver` -> `ConstraintValidator`) so the names stop
    // claiming proof-ness; the artifact is IDENTICAL, so the gate counts
    // BOTH names — the old one survives only as a doc(hidden) alias for
    // the dirty-at-rename `circuit/src/lib.rs` re-exports.
    "TraceSummary",
    "generate_unchecked",
    "simulated_proof_size_bytes",
];

fn is_ident_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// ⚑ WHY THIS IS NOT `src.matches(p)` — THE SUBSTRING SCAN PRODUCED TWO FALSE REDS AND
/// THE SECOND ONE WAS READ AS A TRUE ONE (both measured 2026-08-07, both at HEAD).
///
/// 1. **A LONGER IDENTIFIER CONTAINED A PATTERN.** `"ConstraintProof"` is a substring of
///    `"RootConstraintProof"`, so `fhegg-fhe/src/private_book_canonical_backend.rs`
///    (:735,:746,:749) counted 3 mock sites — for a struct whose `proof` field is a REAL
///    Bulletproofs `LinearProof`, decoded by `LinearProof::from_bytes`. Not one byte of
///    that file rides a mock prover. It was a NEW-file violation, i.e. the loudest verdict
///    this gate has.
///
/// 2. **A TOMBSTONE COMMENT COUNTED AS SURFACE.** `8fea96e71` (2026-08-06) DELETED a dead
///    zero-constraint `impl Air for PresentationAir` and wrote a comment explaining that the
///    `Air` trait is consumed only by `TraceSummary::{generate, generate_unchecked,
///    from_trace}`. Two names, in prose, describing a deletion — and `circuit/src/presentation.rs`
///    went 11 -> 13 and reported `GREW: the purge only shrinks`. **A commit that removed mock
///    surface was accused of adding it.** The 11 CODE sites were untouched (verified by
///    counting `8fea96e71^` and `8fea96e71` under this matcher: 11 and 11).
///
/// So the gate counts **code identifiers**, not text: comments are blanked, and a match must
/// sit on Rust identifier boundaries.
///
/// ⚠ IT MUST NOT UNDER-COUNT. Blanking comments is the fail-OPEN direction of this gate, so
/// the blanker TRAVERSES string and char literals rather than ignoring them — otherwise a
/// `"http://…"` in production source would open a line comment and swallow every real site
/// after it. `matcher_blanks_comments_without_swallowing_code` is that falsifier, and
/// `blank_comments` is length-preserving so a drift cannot hide in it.
fn blank_comments(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = b.to_vec();
    let mut i = 0usize;
    let blank = |out: &mut Vec<u8>, at: usize| {
        if out[at] != b'\n' {
            out[at] = b' ';
        }
    };
    while i < b.len() {
        match b[i] {
            // line comment (covers `//`, `///` and `//!`)
            b'/' if b.get(i + 1) == Some(&b'/') => {
                while i < b.len() && b[i] != b'\n' {
                    blank(&mut out, i);
                    i += 1;
                }
            }
            // block comment — Rust nests them
            b'/' if b.get(i + 1) == Some(&b'*') => {
                let mut depth = 0usize;
                while i < b.len() {
                    if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
                        depth += 1;
                        blank(&mut out, i);
                        blank(&mut out, i + 1);
                        i += 2;
                    } else if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
                        depth = depth.saturating_sub(1);
                        blank(&mut out, i);
                        blank(&mut out, i + 1);
                        i += 2;
                        if depth == 0 {
                            break;
                        }
                    } else {
                        blank(&mut out, i);
                        i += 1;
                    }
                }
            }
            // raw string `r"…"` / `r#"…"#` — TRAVERSED, not blanked
            b'r' if matches!(b.get(i + 1), Some(&b'"') | Some(&b'#')) => {
                let mut j = i + 1;
                let mut hashes = 0usize;
                while b.get(j) == Some(&b'#') {
                    hashes += 1;
                    j += 1;
                }
                if b.get(j) == Some(&b'"') {
                    j += 1;
                    while j < b.len() {
                        if b[j] == b'"' {
                            let mut k = j + 1;
                            let mut seen = 0usize;
                            while seen < hashes && b.get(k) == Some(&b'#') {
                                seen += 1;
                                k += 1;
                            }
                            if seen == hashes {
                                j = k;
                                break;
                            }
                        }
                        j += 1;
                    }
                    i = j;
                } else {
                    // a plain identifier starting with `r`
                    i += 1;
                }
            }
            // normal string — TRAVERSED, not blanked
            b'"' => {
                i += 1;
                while i < b.len() {
                    if b[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if b[i] == b'"' {
                        i += 1;
                        break;
                    }
                    i += 1;
                }
            }
            // char literal `'x'` / `'\n'`, but NOT a lifetime (`'a`): only skip when a
            // closing quote is within reach on the same line.
            b'\'' => {
                let mut j = i + 1;
                if b.get(j) == Some(&b'\\') {
                    j += 1;
                    while j < b.len() && b[j] != b'\'' && b[j] != b'\n' && j - i < 12 {
                        j += 1;
                    }
                } else if j < b.len() {
                    j += 1;
                }
                if b.get(j) == Some(&b'\'') {
                    i = j + 1;
                } else {
                    i += 1;
                }
            }
            _ => i += 1,
        }
    }
    // The blanker only ever overwrites bytes in place, so this cannot fail; the fallback
    // is the SAFE (over-counting) direction rather than an empty haystack.
    String::from_utf8(out).unwrap_or_else(|_| src.to_string())
}

/// Count `needle` in `hay`, requiring Rust-identifier boundaries wherever the needle's own
/// edge is an identifier byte. `prove_ivc(` needs only a left boundary (`(` already ends the
/// identifier); `ConstraintProof` needs both, which is what stops `RootConstraintProof`.
fn count_ident_bounded(hay: &str, needle: &str) -> usize {
    let (h, n) = (hay.as_bytes(), needle.as_bytes());
    if n.is_empty() || n.len() > h.len() {
        return 0;
    }
    let check_left = is_ident_byte(n[0]);
    let check_right = is_ident_byte(n[n.len() - 1]);
    let mut count = 0usize;
    for i in 0..=(h.len() - n.len()) {
        if &h[i..i + n.len()] != n {
            continue;
        }
        let left_ok = !check_left || i == 0 || !is_ident_byte(h[i - 1]);
        let end = i + n.len();
        let right_ok = !check_right || end >= h.len() || !is_ident_byte(h[end]);
        if left_ok && right_ok {
            count += 1;
        }
    }
    count
}

fn count_mock_sites(src: &str) -> usize {
    let code = blank_comments(src);
    MOCK_PATTERNS
        .iter()
        .map(|p| count_ident_bounded(&code, p))
        .sum()
}

/// Frozen 2026-07-16. Verdicts from the purge map (`wh0frxr57`). **SHRINK ONLY.**
#[rustfmt::skip]
const BASELINE: &[(&str, usize)] = &[
        // ── THE MOCK ENGINES themselves (retire once nothing production rides them) ──
        // 2026-07-16: presentation-IVC surface retired (`IvcPresentationProof` + verify,
        // `IvcBackend`/`IvcBackendProof`/`finalize_with_backend`): 79 -> 70.
        // circuit/src/ivc.rs: PURGED 2026-07-16 (final cut) — the simulated engine ITSELF is
        // DELETED (prove/verify/builder/proof types/IvcAir/create_test_chain, plus its dead
        // riders: cipherclerk's never-enabled `enable_ivc` path, the soundness.rs mock tests,
        // the ivc_attenuation_chain example). 70 -> 0. What remains in ivc.rs are the REAL
        // Poseidon2 hash-chain primitives + the state-transition trace shape, which contain
        // zero mock sites.
        // 2026-07-17: renamed to VALIDATOR names (`ConstraintValidator`/`TraceSummary`,
        // legacy aliases kept for lib.rs); dead `proof_size_display` deleted; counts under
        // the widened pattern set (old + "TraceSummary"): 17 -> 15. Still SHRINK ONLY.
        // 2026-08-07: 15 -> 11 under the identifier matcher (4 doc-comment hits dropped).
        ("circuit/src/constraint_prover.rs", 11),
        // node/src/mcp/handlers_verify.rs: PURGED 2026-07-16 — dregg_compress_history now proves via
        // the REAL prove_turn_chain_recursive over retained FinalizedTurns (plumbed at the node commit
        // path); dregg_compose_proofs retired fail-closed. 3 -> 0.
        // dregg-genesis-snapshot: PURGED 2026-07-16 — the mock "history proof" field was DROPPED
        // (not renamed): the layer holds no per-turn provable data, and the leg was minterable by
        // any forger. Tamper-refusal rests on the voucher/re-addressing consistency checks, and
        // the crate's docs now say exactly what those are NOT.
        // ── WIRE-FEASIBLE (real data trivially available here) ──
        // preflight/src/checks/sovereign.rs: PURGED 2026-07-16 — the ivc_history_compression check
        // now mints REAL rotated turns (rotation_witness) and drives the REAL whole-chain fold
        // (`ivc_turn_chain::prove_turn_chain_recursive` + `verify_whole_chain_proof_bytes`), with
        // forged-chain / tampered-publics / wrong-anchor refusal teeth.
        // preflight/src/checks/{proofs,composition,backends}.rs: PURGED 2026-07-16 (d17cbdfe9) — the
        // promotion gate's IVC checks (ivc, ivc_wrong_root, chain, ivc-recursive) now verify the shared
        // REAL whole-chain fold (`preflight/src/checks/ivc_real.rs`, ONE minter) via
        // `verify_whole_chain_proof_bytes`, each with a refusal tooth (wrong genesis root, relabeled
        // num_turns, tampered chain_digest). proofs 5->0, composition 2->0, backends 2->0.
        // ── HONEST-RETIRE (dead but ARMED: the mock rode wire types / is_valid honored it) ──
        // 2026-07-16 the presentation-IVC path was RETIRED: `PresentationAir::prove_ivc`/
        // `prove_ivc_no_folds`, `BridgePresentationBuilder::prove_ivc`, `IvcPresentationProof`,
        // and the `ivc_proof` wire field are DELETED; `is_valid()` now rests solely on
        // `real_stark_proof`. bridge/src/present.rs: 4 -> 0.
        // circuit/src/multi_step_witness.rs: 3 -> 0 (`prove_authorization` trace-digest leg gone).
        // circuit/src/backends/mod.rs: 2 -> 0 (unimplemented `IvcBackend` trait gone).
        // presentation.rs residual 11 = the sequential `prove()` fold-proof path (constraint
        // proofs inside `PresentationProof`), still exercised by prove()/prove_fast(); retires
        // with the constraint-prover engine itself.
        ("circuit/src/presentation.rs", 11),
        // ── incidental ──
        ("circuit/src/lib.rs", 1),
        // 2026-08-07, RE-MEASURED UNDER THE IDENTIFIER MATCHER (see `blank_comments`). These
        // numbers move DOWN and only down; the code they describe did not change on this day.
        // What changed is that the gate stopped counting prose:
        //   constraint_prover.rs  15 -> 11  (4 hits were `//!`/`///` doc lines — :6, :10, :13, :245)
        //   presentation.rs       13 -> 11  (the 2 hits `8fea96e71` added were a TOMBSTONE comment)
        //   derivation_descriptor.rs 1 -> 0  and is DELETED FROM THIS LIST — its single hit was
        //       the `//!` line :71, which is the whole reason it was ever here ("names the mock
        //       only to REFUSE it"). A file whose only mock mention is prose is not a baseline
        //       entry; if real mock surface ever lands there it must appear as a NEW violation.
        //   private_book_canonical_backend.rs 3 -> 0 — `RootConstraintProof`, a REAL Bulletproofs
        //       `LinearProof` carrier. It was never on this list and must never be.
];

#[test]
fn no_new_production_surface_rides_a_mock_prover() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let mut violations = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            // ⚠ `file_type()` does NOT follow symlinks, and that is the point. A local tree
            // carries `metatheory/.lake/.lake -> metatheory/.lake`, a self-referential link;
            // `Path::is_dir()` follows it, so the walk descended into itself and only stopped
            // when the accumulated path hit the OS limit — ~2 minutes of pointless recursion
            // whose TERMINATION depended on PATH_MAX. No Rust production source in this tree
            // sits behind a symlinked directory (the only ones are `node_modules`, a sel4
            // prefix, and that `.lake` loop), so skipping them costs the scan nothing.
            if e.file_type().map(|t| t.is_symlink()).unwrap_or(true) {
                continue;
            }
            if p.is_dir() {
                // production source only: skip test/bench/example trees and build output
                if !matches!(
                    name.as_str(),
                    "target" | ".git" | "tests" | "benches" | "examples" | "node_modules"
                ) {
                    stack.push(p);
                }
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") || name == "tests.rs" {
                continue;
            }
            let Ok(src) = std::fs::read_to_string(&p) else {
                continue;
            };
            let n = count_mock_sites(&src);
            if n == 0 {
                continue;
            }
            let rel = p
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            match BASELINE.iter().find(|(f, _)| *f == rel) {
                None => violations.push(format!(
                    "  NEW production surface rides a MOCK prover: {rel} ({n} sites)\n     -> wire it to `ivc_turn_chain::prove_turn_chain_recursive` / `prove_vm_descriptor2`, or FAIL CLOSED. Do NOT add it to the baseline."
                )),
                Some((_, allowed)) if n > *allowed => violations.push(format!(
                    "  GREW: {rel} ({allowed} -> {n} mock sites)\n     -> the purge only shrinks. Wire it to the real prover."
                )),
                _ => {}
            }
        }
    }
    assert!(
        violations.is_empty(),
        "\n\nMOCK-PROOF PURGE VIOLATED — production must never ride a mock prover.\n\n{}\n\nSee this file's module docs for the real prover + the honest fail-closed pattern.\n",
        violations.join("\n")
    );
}

// ─────────────────────── FALSIFIERS FOR THE MATCHER ITSELF ───────────────────────
//
// ⚑ THE GATE'S VERDICT IS ONLY AS GOOD AS `count_mock_sites`, AND FOR THREE WEEKS NOTHING
// TESTED IT. A ratchet whose *counter* is untested reports on a quantity nobody has ever
// checked; both false reds above were invisible for exactly that reason. These are the
// counter's teeth: each one FAILS under the old `src.matches(p).count()`.

/// A real Bulletproofs carrier whose type name merely CONTAINS a pattern is not mock
/// surface. This is the false red that made `fhegg-fhe` look like a new violation.
#[test]
fn matcher_does_not_flag_a_longer_identifier() {
    let real = r#"
        root_constraint_proofs.push(RootConstraintProof { image, proof });
        root_constraint_proofs: Vec<RootConstraintProof>,
        struct RootConstraintProof { proof: LinearProof }
    "#;
    assert_eq!(
        count_mock_sites(real),
        0,
        "`RootConstraintProof` carries a REAL Bulletproofs `LinearProof`; the gate must not \
         count it just because `ConstraintProof` is a substring of its name"
    );

    // …and the genuine identifier is STILL caught, so the boundary rule did not disarm it.
    assert_eq!(
        count_mock_sites("pub type ConstraintProof = TraceSummary;"),
        2,
        "a real `ConstraintProof`/`TraceSummary` site must still count"
    );
    assert_eq!(
        count_mock_sites("let p = TraceSummary::generate_unchecked(&air);"),
        2,
        "a real unchecked-summary call site must still count"
    );
}

/// Prose about a mock — especially a tombstone for one that was DELETED — is not surface.
/// This is the false red that turned `8fea96e71`'s deletion into a `GREW` verdict.
#[test]
fn matcher_does_not_count_prose() {
    let tombstone = r#"
        // DELETED: the `Air` trait is consumed only by
        // `TraceSummary::{generate, generate_unchecked, from_trace}`, and NO call site
        /// A doc comment naming ConstraintProof and simulated_proof_size_bytes.
        //! A module doc naming prove_ivc( and create_test_chain(.
        /* a block /* nested */ comment naming TraceSummary */
    "#;
    assert_eq!(
        count_mock_sites(tombstone),
        0,
        "comments describing a mock (or its removal) are prose, not a production surface"
    );
}

/// ⚠ THE FAIL-OPEN DIRECTION. Blanking comments is the only thing here that can make the
/// gate see LESS than exists, so the blanker must know a `//` inside a string is not a
/// comment. A naive line-comment stripper swallows the rest of the line — and the rest of
/// the line is where the real site sits.
#[test]
fn matcher_blanks_comments_without_swallowing_code() {
    let s = "let url = \"https://example.invalid/x\"; let p = TraceSummary::generate(&a);";
    assert_eq!(
        count_mock_sites(s),
        1,
        "a `//` inside a string literal must not open a comment and hide the code after it"
    );

    let raw = "let s = r#\"// not a comment: TraceSummary\"#; let q = ConstraintProof::new();";
    assert_eq!(
        count_mock_sites(raw),
        2,
        "a raw string is traversed, not stripped — the sites inside AND after it stay visible"
    );

    // Lifetimes must not be mistaken for char literals (that would desynchronise the scan).
    let lifetimes = "fn f<'a>(x: &'a str) -> &'a str { x } // TraceSummary\nlet z = TraceSummary::generate(&a);";
    assert_eq!(count_mock_sites(lifetimes), 1);

    // Length preservation: the blanker overwrites in place and never shifts an offset.
    for src in [s, raw, lifetimes, "/* a */ b // c\n'x' '\\n'"] {
        assert_eq!(
            blank_comments(src).len(),
            src.len(),
            "blank_comments must be length-preserving"
        );
    }
}

/// ⚑ PINNED AGAINST THE REAL TREE, not a synthetic string. If the matcher ever regresses to
/// a substring scan, THESE are the two files that go wrong first — and this says so by name
/// instead of leaving a future reader to re-derive it from a red baseline diff.
#[test]
fn the_two_files_that_the_substring_scan_got_wrong() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();

    let bp = root.join("fhegg-fhe/src/private_book_canonical_backend.rs");
    let bp_src = std::fs::read_to_string(&bp).expect("private_book_canonical_backend.rs exists");
    assert!(
        bp_src.contains("RootConstraintProof"),
        "this test is only meaningful while that file still carries the name that broke the \
         old matcher; if `RootConstraintProof` was renamed, re-point or retire this tooth"
    );
    assert_eq!(
        count_mock_sites(&bp_src),
        0,
        "the private-book backend rides a REAL Bulletproofs `LinearProof`; it must not appear \
         as a mock-prover violation"
    );

    let pr = root.join("circuit/src/presentation.rs");
    let pr_src = std::fs::read_to_string(&pr).expect("presentation.rs exists");
    assert_eq!(
        count_mock_sites(&pr_src),
        11,
        "presentation.rs's mock surface is the 11 CODE sites of the sequential prove() fold \
         path. A raw substring scan reads 13 because a tombstone comment names two of the \
         identifiers it describes deleting."
    );
}
