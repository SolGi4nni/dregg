#!/usr/bin/env python3
"""check-silent-skip.py — a test that did not exercise its subject must not report `ok`.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
`scripts/check-bare-ignore.py` proved this tree's `#[ignore]` population is clean:
270 attributes, 270 reason strings, zero bare. What it could not see is the shape
NEXT DOOR, which is strictly worse:

    #[test]
    fn the_verified_gate_rejects_a_forged_grant() {
        if !dregg_lean_ffi::lean_available() { return; }   // <- no archive today
        ...the entire point of the test...
    }

An `#[ignore]` prints `ignored`. THIS prints `ok`. The tree already says so, in the
reason string of an ignore it chose over exactly this shape:

    redteam/tests/devnet_adversarial.rs:91
      "… Without it this asserts NOTHING — an #[ignore] reports `ignored` (honest),
       not `ok` (a lie)."

The population is concentrated in `exec-lean` and `dregg-lean-ffi`, the two suites
that guard the verified Lean cores. A green there is a claim about a machine-checked
kernel, and on a box without `libdregg_lean.a` it is a claim nobody checked.

═══ WHAT IT LOOKS FOR ═════════════════════════════════════════════════════════════
A `#[test]` / `#[tokio::test]` / `#[gpui::test]` function that can reach a `return`
(or `return Ok(())`) which

  * exits the TEST FUNCTION — not a nested `fn` item, not a closure, not an inner
    `async` block. Those returns are ordinary control flow and are excluded by
    walking the brace stack and classifying each block's OPENER.
  * is reached with NO assertion executed before it. `assert*!`, `panic!` and
    friends count as "this test asserted something"; `.unwrap()`/`.expect()` do NOT,
    because in this tree they are setup, and counting them excuses a test that builds
    a whole ledger and then bails without asking the verified kernel anything.
  * is controlled by an ENVIRONMENT / AVAILABILITY predicate — `*_available()`,
    `env::var`, `Path::exists`, `demand_lean`, a `Command` probe — INCLUDING one
    reached through a per-crate bool helper (`skip_no_lean`, `ensure_oracle`,
    `skip_if_core_unlinked`). Keying on direct probes alone found 15 of exec-lean's
    41 sites; the rest were one call away and read as opaque identifiers.

Plus the shape with no `return` at all, which a return-only census reads as clean:

    #[test]
    fn t() { if lean_available() { assert!(the_verified_thing()); } }

Also `#[ignore]`d tests are EXCLUDED — they already print `ignored`, which is true.

═══ ⚠ WHY THIS IS NOT A GREP ══════════════════════════════════════════════════════
Same reason `check-bare-ignore.py` is not: this tree writes ABOUT its own skips
constantly, in doc comments ("honestly skips when the archive is absent") and in
panic strings ("would have SILENTLY SKIPPED … and reported `ok`"). A textual scan
counts the documentation of the disease as the disease. So this reads source with
comments, strings and char literals BLANKED by
`check-production-callers.py::strip_noise` — borrowed, not re-grown, offsets
preserved so every line number still indexes the original file.

═══ THE VERDICTS ══════════════════════════════════════════════════════════════════
  SILENT     reports `ok` having asserted nothing. ZERO TOLERANCE — the tree is at
             zero as of 2026-07-27 and there is no baseline row that can excuse one.
  DEMANDED   routes through `dregg_lean_ffi::demand_lean`, which PANICS by default
             (`DREGG_TEST_ALLOW_MISSING_LEAN=1` opts out, visibly). Safe by
             construction, so it needs no baseline.
  INVERSE    the test's subject IS the fixture's ABSENCE, so it skips when the
             fixture is PRESENT. Demanding availability is backwards for it. A real
             but DIFFERENT hole; baselined.
  REENTRANT  one half of a two-process test — the parent re-execs the binary with
             `--exact <fn>` + a marker env var and the child does the work. The
             assertions do happen; baselined with its residual named.
  ASSERTED   returns, but after asserting something. Not a defect.

═══ THE FLOOR ═════════════════════════════════════════════════════════════════════
"No silent skips" is a NEGATIVE assertion, and a broken reader satisfies it
perfectly. This gate's OWN first cut proved it: one off-by-one in `find_body` made it
report ZERO findings across 20 000 tests and the headline read clean. So it also
asserts it FOUND at least MIN_TESTS test functions and MIN_GUARDED guard-shaped
skips, and `--self-test` drives both floors red rather than merely declaring them.

Usage:
    scripts/check-silent-skip.py                # the gate
    scripts/check-silent-skip.py --report       # the whole population
    scripts/check-silent-skip.py --by-crate     # counts by crate and guard shape
    scripts/check-silent-skip.py --self-test    # can it go red?
    scripts/check-silent-skip.py --bless        # rewrite the baseline
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BASELINE = REPO / "baseline" / "silent-skip.tsv"

# ── the Rust blanker, borrowed rather than re-grown ────────────────────────────────
_PC_PATH = REPO / "scripts" / "check-production-callers.py"
_spec = importlib.util.spec_from_file_location("_pc", _PC_PATH)
if _spec is None or _spec.loader is None:  # pragma: no cover
    sys.exit(f"UNAVAILABLE: cannot load the Rust blanker at {_PC_PATH}")
pc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pc)

SKIP_DIR_PARTS = {
    ".git", "target", ".lake", "node_modules", ".claude",
    ".cargo", "dist", ".venv", "__pycache__", "metatheory", "vendor",
    "ts-sdk.archived", "site-old-scavenge", "old-docs",
}

# Population measured 2026-07-27. See THE FLOOR.
MIN_TESTS = 12000
MIN_GUARDED = 60

TEST_ATTR = re.compile(r"#\s*\[\s*(?:[a-z_]+\s*::\s*)*test\s*\]")
FN_DECL = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*[(<]")

# A `return` that leaves the test function.
RETURN_TOK = re.compile(r"\breturn\b")

# Anything that makes the test have ASSERTED before it bails.
#
# ⚠ `.expect(` / `.unwrap()` are DELIBERATELY NOT HERE. They fail the test if they
# fire, but in this tree they are overwhelmingly SETUP — `read_to_string(golden)
# .expect("fixture")`, `Ledger::new().insert_cell(c).unwrap()`. Counting them as
# "the test asserted something" excuses exactly the shape being hunted: a test that
# builds a ledger, then bails on `!lean_available()` without ever asking the verified
# kernel anything. That is a silent skip with a tidy prologue.
ASSERTION = re.compile(
    r"\bassert(?:_eq|_ne|_matches|_matches_regex)?\s*!"
    r"|\bdebug_assert(?:_eq|_ne)?\s*!"
    r"|\bpanic\s*!"
    r"|\bunreachable\s*!"
    r"|\btodo\s*!"
    r"|\bunimplemented\s*!"
    r"|\bprop_assert(?:_eq|_ne)?\s*!"
)

# ── guard shapes ───────────────────────────────────────────────────────────────────
# Ordered: the FIRST match names the shape, so the specific ones come first.
GUARD_SHAPES: list[tuple[str, re.Pattern[str]]] = [
    ("demand_lean", re.compile(r"\bdemand_lean\w*\s*\(")),
    ("demand_or_skip", re.compile(r"\bdemand_or_skip\w*\s*\(")),
    ("skip_if_*", re.compile(r"\bskip_if_\w+\s*\(")),
    ("*_available()", re.compile(r"\b\w*_?available\s*\(")),
    ("*_present()", re.compile(r"\b\w*_?present\s*\(")),
    ("*_linked()/unlinked", re.compile(r"\b\w*_?(?:un)?linked\s*\(")),
    ("*_enabled()", re.compile(r"\b\w*_?enabled\s*\(")),
    ("*_installed()", re.compile(r"\b\w*_?installed\s*\(")),
    ("*_reachable()/running", re.compile(r"\b\w*_?(?:reachable|running|alive|up)\s*\(")),
    ("env::var", re.compile(r"\benv\s*::\s*var(?:_os)?\s*\(|\bvar(?:_os)?\s*\(\s*[A-Z_\s]*\)")),
    ("option_env!", re.compile(r"\boption_env\s*!")),
    ("Path::exists", re.compile(r"\.exists\s*\(\s*\)|\btry_exists\s*\(")),
    ("Command probe", re.compile(r"\bCommand\s*::\s*new\b|\bwhich\s*\(|\.output\s*\(\s*\)|\.status\s*\(\s*\)")),
    ("has_*/have_*", re.compile(r"\bha(?:s|ve)_\w+\s*\(")),
    ("*_supported()", re.compile(r"\b\w*_?supported\s*\(")),
    ("feature/cfg probe", re.compile(r"\bcfg\s*!\s*\(|\bfeature\s*=")),
    ("fixture/golden load", re.compile(r"\b(?:read_to_string|read_dir|File\s*::\s*open|fs\s*::\s*read)\s*\(")),
]

# Names that make an identifier a plausible availability probe even without `()`.
AVAIL_WORDS = re.compile(
    r"\b\w*(?:available|present|linked|enabled|installed|reachable|running|"
    r"supported|exists|configured|armed|seeded|provisioned)\b",
    re.I,
)


def rust_files() -> list[Path]:
    out = [
        p for p in REPO.rglob("*.rs")
        if not any(part in SKIP_DIR_PARTS for part in p.relative_to(REPO).parts)
    ]
    out.sort()
    return out


def crate_of(rel: Path) -> str:
    """The crate directory a path belongs to (first path component, or two for nested)."""
    parts = rel.parts
    if len(parts) > 1 and parts[0] in {
        "starbridge-apps", "demo", "sel4", "tools", "deploy", "mobile", "orb",
    }:
        return "/".join(parts[:2])
    return parts[0]


class Block:
    """One `{` on the brace stack, remembering what OPENED it."""

    __slots__ = ("start", "kind")

    def __init__(self, start: int, kind: str):
        self.start = start
        self.kind = kind


CLOSURE_OPENER = re.compile(r"(?:\|[^|{}]*\||\|\|)\s*(?:->\s*[^{;]+?)?\s*$")
NESTED_FN_OPENER = re.compile(r"\bfn\s+[A-Za-z_]\w*\s*(?:<[^{}]*>)?\s*\([^{}]*\)\s*(?:->[^{}]*?)?\s*$")
ASYNC_BLOCK_OPENER = re.compile(r"\basync\s+(?:move\s+)?$")


def opener_kind(text: str, brace_pos: int) -> str:
    """Classify what a `{` opens, by the ~200 chars before it."""
    look = text[max(0, brace_pos - 240):brace_pos]
    if NESTED_FN_OPENER.search(look):
        return "fn"
    if ASYNC_BLOCK_OPENER.search(look):
        return "async"
    if CLOSURE_OPENER.search(look):
        return "closure"
    return "block"


def find_body(text: str, fn_paren: int) -> tuple[int, int] | None:
    """Given the offset of the `(` or `<` that follows `fn NAME`, return the body span.

    `fn_paren` must index the OPENING delimiter itself (FN_DECL's last character), not
    one past it — starting one past leaves the paren counter at -1 for the whole
    signature and every body then reads as unfindable, which is a silent zero-finding
    census. It read as clean; it was blind.
    """
    # Walk to the `{` that opens the body, skipping the parameter list, generics and
    # the return type. A `{` inside the return type (e.g. `impl Fn() { }`) does not
    # occur in a test signature, which takes no arguments and returns `()` or a Result.
    i = fn_paren
    depth_paren = 0
    depth_angle = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c == "(":
            depth_paren += 1
        elif c == ")":
            depth_paren -= 1
        elif c == "<" and depth_paren == 0:
            depth_angle += 1
        elif c == ">" and depth_paren == 0 and depth_angle:
            depth_angle -= 1
        elif c == ";" and depth_paren == 0 and depth_angle == 0:
            return None  # a trait-method declaration, no body
        elif c == "{" and depth_paren == 0 and depth_angle == 0:
            break
        i += 1
    if i >= n:
        return None
    open_pos = i
    depth = 0
    while i < n:
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return (open_pos, i)
        i += 1
    return None


def escaping_returns(text: str, open_pos: int, close_pos: int) -> list[int]:
    """Offsets of `return` tokens that exit the FUNCTION whose body is [open,close].

    A `return` inside a nested `fn` item, a closure, or an `async` block belongs to
    that construct and is excluded — this is where a naive scan invents defects.
    """
    stack: list[Block] = []
    out: list[int] = []
    i = open_pos
    while i <= close_pos:
        c = text[i]
        if c == "{":
            stack.append(Block(i, "body" if i == open_pos else opener_kind(text, i)))
        elif c == "}":
            if stack:
                stack.pop()
        elif c == "r" and RETURN_TOK.match(text, i):
            if not any(b.kind in ("fn", "closure", "async") for b in stack):
                out.append(i)
            i += len("return")
            continue
        i += 1
    return out


def guard_context(text: str, ret_pos: int, body_start: int) -> str:
    """The controlling expression for an early return, approximated.

    Walk back to the innermost enclosing `{` and take the source from a bit before it
    up to the return: that spans the `if <cond> {`, the `else {` of a `let … else`,
    or the `<pat> => {` of a match arm. 400 chars is enough for every real shape in
    this tree and short enough not to swallow an unrelated earlier statement.
    """
    depth = 0
    i = ret_pos - 1
    while i > body_start:
        if text[i] == "}":
            depth += 1
        elif text[i] == "{":
            if depth == 0:
                break
            depth -= 1
        i -= 1
    lo = max(body_start, i - 400)
    return text[lo:ret_pos]


# ── INDIRECT guards: the probe lives in a local helper ─────────────────────────────
# The dominant real shape in this tree is NOT `if !lean_available() { return; }` — it
# is a per-file bool helper that wraps the probe:
#
#     fn skip_no_lean() -> bool { !demand_lean(lean_available(), "…") }
#     fn ensure_oracle() -> bool { … constraint_admits_available() … }
#     #[test] fn t() { if skip_no_lean() { return; } … }
#
# Reading only the call site, `skip_no_lean()` is an opaque identifier and the census
# reports the file clean. Measured: keying on direct probes alone MISSED 26 of the 41
# `demand_lean` sites in `exec-lean` — a census that found a third of the population
# and said nothing about the rest. So pass 1 collects bool-returning helpers whose own
# body probes the environment, and pass 2 treats a call to one as the guard it is.
HELPER_DECL = re.compile(
    r"\bfn\s+([A-Za-z_]\w*)\s*\([^()]*\)\s*->\s*bool\s*\{"
)
_HELPER_CACHE: dict[str, str] = {}


def collect_guard_helpers(text: str) -> dict[str, str]:
    """name -> guard shape, for bool helpers in `text` that probe the environment."""
    out: dict[str, str] = {}
    for m in HELPER_DECL.finditer(text):
        brace = m.end() - 1
        depth, i = 0, brace
        while i < len(text):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        body = text[brace:i]
        if len(body) > 4000:
            continue
        for shape, pat in GUARD_SHAPES:
            if pat.search(body):
                out[m.group(1)] = shape
                break
    return out


def classify_guard(ctx: str, helpers: dict[str, str] | None = None) -> str | None:
    # ⚠ HELPERS FIRST. A helper's BODY is better evidence than its NAME, and the two
    # disagree in the case that matters: `bridge`'s guard is called
    # `skip_if_core_unlinked()`, which the name-shaped `skip_if_*` pattern claims — so
    # the census reported five bridge tests SILENT after they had already been routed
    # through `demand_lean`. A gate that cannot see its own repair lands is a gate that
    # gets its repair reverted.
    for name, shape in (helpers or {}).items():
        if re.search(r"(?<![A-Za-z0-9_])" + re.escape(name) + r"\s*\(", ctx):
            return f"{shape} (via {name})"
    for name, pat in GUARD_SHAPES:
        if pat.search(ctx):
            return name
    if AVAIL_WORDS.search(ctx):
        return "avail-named ident"
    return None


class Finding:
    __slots__ = ("rel", "line", "fn_name", "verdict", "shape", "crate")

    def __init__(self, rel, line, fn_name, verdict, shape):
        self.rel = rel
        self.line = line
        self.fn_name = fn_name
        self.verdict = verdict
        self.shape = shape
        self.crate = crate_of(rel)

    def key(self) -> tuple[str, str]:
        return (str(self.rel), self.fn_name)


DEMANDED = re.compile(r"\bdemand_lean\w*\s*\(|\bdemand_or_skip\w*\s*\(|\brequire_\w+\s*\(")

# ── two shapes that LOOK like the disease and are not ──────────────────────────────
#
# INVERSE: the test's subject IS the fixture's ABSENCE — `fails_closed_when_the_
# archive_is_absent` asserts the fail-closed posture, so it skips when the archive is
# PRESENT. `demand_lean` is exactly backwards for it, and panicking would break the
# one test that checks what happens on a marshal-only build. It is still a real hole
# (on a provisioned box it reports `ok` having asserted nothing) but a DIFFERENT one,
# whose fix is injecting unavailability rather than demanding availability.
#
# ⚠ Keyed on the ABSENCE sense, not on `fail_closed`. A bare `fails?_closed`
# alternative would have claimed `bridge`'s `reached_consensus_is_fail_closed_per_rung`
# — an ordinary positive-polarity gate — and relabelled a real finding as a residual.
# The two genuine members both say `_when_…_absent`.
INVERSE_NAME = re.compile(
    r"_(?:when|unless|if)_.*_(?:absent|unavailable|missing|unlinked|not_linked)"
    r"|_(?:absent|unavailable|unlinked)$"
)

# REENTRANT: one half of a two-process test. The parent re-execs the test binary with
# `--exact <this fn>` and a marker env var; the child does the work. Run WITHOUT the
# marker (the normal path) the worker returns immediately — but the assertions do
# happen, in the child, driven by the parent. Naming it separately keeps the SILENT
# count honest in both directions.
#   ⚠ residual: the worker half still prints `ok` in the PARENT process. Closing that
#   means `#[ignore]` on the worker AND `--ignored` added to the parent's spawn args,
#   since libtest's `--exact` will not run an ignored test.
CHILD_SPAWN = re.compile(r"current_exe\s*\(\s*\)")


IF_TOK = re.compile(r"\bif\b")


def toplevel_guard_ifs(
    text: str, open_pos: int, close_pos: int, helpers: dict[str, str]
) -> tuple[str, int] | None:
    """The WRAPPED-IF shape: no `return` anywhere, the work just does not happen.

        #[test]
        fn t() {
            if lean_available() {
                assert!(the_verified_thing());   // <- the entire test
            }
        }

    This never returns early because it never needs to; on a box without the archive
    the body is skipped and cargo prints `ok`. It is the same lie with no `return`
    token to find, so a return-only census reads it clean.

    Returns (shape, line_offset) when every assertion in the test lives inside one
    guard-conditioned `if`/`else` chain and none lives outside it.
    """
    body = text[open_pos:close_pos + 1]
    total_asserts = len(ASSERTION.findall(body))
    if total_asserts == 0:
        return None

    stack_depth = 0
    i = open_pos
    while i <= close_pos:
        c = text[i]
        if c == "{":
            stack_depth += 1
        elif c == "}":
            stack_depth -= 1
        elif c == "i" and IF_TOK.match(text, i) and stack_depth == 1:
            # Condition runs from `if` to the `{` that opens its block.
            j, d = i + 2, 0
            while j <= close_pos:
                if text[j] in "([":
                    d += 1
                elif text[j] in ")]":
                    d -= 1
                elif text[j] == "{" and d == 0:
                    break
                j += 1
            if j > close_pos:
                break
            cond = text[i:j]
            shape = classify_guard(cond, helpers)
            # Walk the whole if/else-if/else chain — an `else` branch runs too, so
            # assertions there are NOT skipped.
            chain_start = i
            k = j
            has_asserting_final_else = False
            while True:
                blk_open = k
                d2 = 0
                while k <= close_pos:
                    if text[k] == "{":
                        d2 += 1
                    elif text[k] == "}":
                        d2 -= 1
                        if d2 == 0:
                            break
                    k += 1
                after = text[k + 1:k + 40].lstrip()
                if after.startswith("else"):
                    nxt = text.find("{", k + 1)
                    if nxt == -1 or nxt > close_pos:
                        break
                    # A BARE `else {` (not `else if`) is the unconditional arm: it runs
                    # on every box the `if` did not. `turn/src/executor/
                    # conservation_oracle.rs::native_no_oracle_fails_closed` is exactly
                    # that — native asserts fail-closed, guest asserts the fallback is
                    # legitimate. Both arms assert; nothing is ever skipped. Calling it
                    # a silent skip would be the census inventing a defect.
                    tail = text[k + 1:nxt]
                    if not re.search(r"\belse\s+if\b", tail):
                        d3, m2 = 0, nxt
                        while m2 <= close_pos:
                            if text[m2] == "{":
                                d3 += 1
                            elif text[m2] == "}":
                                d3 -= 1
                                if d3 == 0:
                                    break
                            m2 += 1
                        if ASSERTION.search(text[nxt:m2]):
                            has_asserting_final_else = True
                    k = nxt
                    continue
                break
            del blk_open
            chain_end = min(k, close_pos)
            inside = text[chain_start:chain_end + 1]
            outside_count = total_asserts - len(ASSERTION.findall(inside))
            if shape and outside_count == 0 and not has_asserting_final_else and ASSERTION.search(inside):
                return (shape, chain_start)
            i = chain_end
        i += 1
    return None


def scan_file(rel: Path, raw: str, helpers: dict[str, str] | None = None) -> tuple[list[Finding], int]:
    """(findings, number of test fns seen)."""
    text = pc.strip_noise(raw)
    helpers = dict(helpers or {})
    helpers.update(collect_guard_helpers(text))
    findings: list[Finding] = []
    seen = 0
    for m in TEST_ATTR.finditer(text):
        fm = FN_DECL.search(text, m.end())
        if not fm:
            continue
        # The `fn` must follow within a short run of further attributes / `async` /
        # `pub`, else this `#[test]` belongs to something else entirely.
        between = text[m.end():fm.start()]
        if between.count("{") or between.count("}") or len(between) > 1200:
            continue
        # An `#[ignore]`d test is ALREADY honest — the harness prints `ignored`, and
        # `check-bare-ignore.py` guarantees it carries a reason. The three redteam
        # devnet tests are the calibration case: they carry BOTH the ignore and an
        # `if !gated() { return; }`, and the ignore's own reason string is the sentence
        # this whole gate is named after. Counting them would be reporting the cure.
        attrs = text[max(0, m.start() - 900):fm.start()]
        if re.search(r"#\s*\[\s*ignore\b", attrs) or re.search(
            r"#\s*\[\s*cfg_attr\s*\([^)]*\bignore\b", attrs
        ):
            continue
        body = find_body(text, fm.end() - 1)
        if not body:
            continue
        seen += 1
        open_pos, close_pos = body
        line = text.count("\n", 0, fm.start()) + 1
        # EVERY escaping return, not just the first: a test that bails on an empty
        # corpus and THEN bails on `!lean_available()` is still a silent skip, and
        # keying on `rets[0]` alone would have called it clean.
        hit = False
        for ret in escaping_returns(text, open_pos, close_pos):
            ctx = guard_context(text, ret, open_pos)
            shape = classify_guard(ctx, helpers)
            if shape is None:
                continue
            prefix = text[open_pos:ret]
            verdict = _verdict(text, ctx, prefix, fm.group(1), shape)
            findings.append(Finding(rel, line, fm.group(1), verdict, shape))
            hit = True
            break
        if hit:
            continue
        wrapped = toplevel_guard_ifs(text, open_pos, close_pos, helpers)
        if wrapped:
            shape, at = wrapped
            ctx = text[at:at + 300]
            verdict = _verdict(text, ctx, "", fm.group(1), shape)
            if verdict == "ASSERTED":
                verdict = "SILENT"
            findings.append(Finding(rel, line, fm.group(1), verdict, f"{shape} [wrapped-if]"))
    return findings, seen


def _helper_is_demanded(shape: str) -> bool:
    return shape.startswith("demand_lean") or shape.startswith("demand_or_skip")


def _verdict(text: str, ctx: str, prefix: str, fn_name: str, shape: str) -> str:
    if ASSERTION.search(prefix):
        return "ASSERTED"
    if DEMANDED.search(ctx) or _helper_is_demanded(shape):
        return "DEMANDED"
    if INVERSE_NAME.search(fn_name):
        return "INVERSE"
    # A child-marker env var the SAME file also sets on a `current_exe()` re-exec.
    if CHILD_SPAWN.search(text):
        for var in re.findall(r"\b([A-Z][A-Z0-9_]{3,})\b", ctx):
            if re.search(r"\.env\s*\(\s*" + var + r"\b", text):
                return "REENTRANT"
        for ident in re.findall(r"\b([a-z_][a-z0-9_]*)\b", ctx):
            if ident.endswith(("_env", "_marker")) and re.search(
                r"\.env\s*\(\s*" + ident + r"\b", text, re.I
            ):
                return "REENTRANT"
    return "SILENT"


def sweep() -> tuple[list[Finding], int]:
    """Two passes. Pass 1 learns the bool helpers that probe the environment — including
    the ones a `tests/common/mod.rs` exports to a whole suite, which a per-file pass
    would see as opaque identifiers. Pass 2 classifies with that vocabulary in hand.

    ⚠ The vocabulary is scoped PER CRATE, not globally. `fn gated() -> bool` is a real
    env probe in `redteam/tests/devnet_adversarial.rs`, and there are seven unrelated
    `gated`s elsewhere in the tree. A global pool would report those as guards on the
    strength of a shared name — findings invented by the instrument, which is the one
    failure mode that gets a gate switched off."""
    files = rust_files()
    sources: dict[Path, str] = {}
    by_crate: dict[str, dict[str, str]] = {}
    for path in files:
        try:
            raw = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if "fn " not in raw:
            continue
        sources[path] = raw
        rel = path.relative_to(REPO)
        by_crate.setdefault(crate_of(rel), {}).update(
            collect_guard_helpers(pc.strip_noise(raw))
        )

    findings: list[Finding] = []
    total_tests = 0
    for path, raw in sources.items():
        if "#[test" not in raw and "::test]" not in raw:
            continue
        rel = path.relative_to(REPO)
        f, seen = scan_file(rel, raw, by_crate.get(crate_of(rel), {}))
        findings.extend(f)
        total_tests += seen
    return findings, total_tests


def read_baseline() -> set[tuple[str, str]]:
    if not BASELINE.exists():
        return set()
    out = set()
    for line in BASELINE.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) >= 3:
            out.add((parts[1], parts[2]))
    return out


def write_baseline(rows: list[Finding]) -> None:
    BASELINE.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# silent-skip.tsv — the NAMED RESIDUALS of the silent-skip sweep.",
        "# Written by scripts/check-silent-skip.py --bless.",
        "#",
        "# This file does NOT hold the disease. SILENT is zero-tolerance and unbaselineable:",
        "# a test that returns on a missing fixture and reports `ok` is a finding, always.",
        "# What lives here are the two shapes that LOOK like it and are not:",
        "#",
        "#   INVERSE    the test's subject IS the fixture's ABSENCE (`fails_closed_when_the_",
        "#              archive_is_absent`), so it skips when the fixture is PRESENT. Demanding",
        "#              availability is backwards. Still a real hole on a provisioned box — the",
        "#              fix is injecting unavailability, not reading the ambient world.",
        "#   REENTRANT  one half of a two-process test: the parent re-execs the binary with",
        "#              `--exact <fn>` + a marker env var and the child does the work. The",
        "#              assertions DO happen. Residual: the worker still prints `ok` in the",
        "#              PARENT process. Closing that needs `#[ignore]` on the worker AND",
        "#              `--ignored` added to the parent's spawn args, since libtest's",
        "#              `--exact` will not run an ignored test.",
        "#",
        "# verdict\tfile\tfn\tguard_shape",
    ]
    for r in sorted(rows, key=lambda r: (r.verdict, str(r.rel), r.fn_name)):
        lines.append(f"{r.verdict}\t{r.rel}\t{r.fn_name}\t{r.shape}")
    BASELINE.write_text("\n".join(lines) + "\n")


# ═══ SELF-TEST ═════════════════════════════════════════════════════════════════════
MUST_CATCH = [
    ("bare_if_return", '''
#[test]
fn t() {
    if !lean_available() { return; }
    assert_eq!(verified(), 1);
}
'''),
    ("let_else_return", '''
#[test]
fn t() {
    let Ok(key) = std::env::var("DREGG_KEY") else { return; };
    assert!(verify(&key));
}
'''),
    ("negated_guard_block", '''
#[test]
fn t() {
    if !std::path::Path::new("fixtures/golden.json").exists() {
        eprintln!("no fixture");
        return;
    }
    assert!(check());
}
'''),
    ("tokio_test", '''
#[tokio::test]
async fn t() {
    if !service_running() { return; }
    assert!(ping().await);
}
'''),
    ("return_ok_unit", '''
#[test]
fn t() -> Result<(), String> {
    if !export_available() { return Ok(()); }
    assert!(exercise()?);
    Ok(())
}
'''),
]

MUST_NOT_CATCH = [
    # The doc comment DESCRIBES the disease. It is not the disease.
    ("prose_about_skipping", '''
/// An unarmed developer build honestly skips when the archive is absent — it would
/// otherwise `return;` on `!lean_available()` and report `ok`, which is a lie.
#[test]
fn t() {
    assert!(verified_thing());
}
'''),
    # The panic MESSAGE names the disease.
    ("prose_in_panic_string", '''
#[test]
fn t() {
    assert!(x, "this would have SILENTLY SKIPPED on !lean_available() and returned ok");
}
'''),
    # A return inside a nested `fn` is that fn's control flow.
    ("return_in_nested_fn", '''
#[test]
fn t() {
    fn helper(p: &Path) -> u32 {
        if !p.exists() { return 0; }
        7
    }
    assert_eq!(helper(Path::new("x")), 0);
}
'''),
    # A return inside a closure is the closure's.
    ("return_in_closure", '''
#[test]
fn t() {
    let f = |p: &Path| {
        if !p.exists() { return 0; }
        7
    };
    assert_eq!(f(Path::new("x")), 0);
}
'''),
    # Asserted first, then bailed: partial work, not a lie.
    ("asserts_before_returning", '''
#[test]
fn t() {
    assert_eq!(parse("1"), 1);
    if !gpu_available() { return; }
    assert!(gpu_path());
}
'''),
    # An early return with no environment predicate at all.
    ("non_guard_early_return", '''
#[test]
fn t() {
    let items = build();
    if items.is_empty() { return; }
    assert!(items.len() > 0);
}
'''),
    # An #[ignore]d test already reports `ignored`. It is the cure, not the disease.
    ("ignored_with_guard_return", '''
#[test]
#[ignore = "live devnet: needs DREGG_DEVNET_REDTEAM=1; an #[ignore] reports `ignored` (honest), not `ok`"]
fn t() {
    if !gated() { return; }
    assert!(the_origin_survives());
}
'''),
    # BOTH arms assert — nothing is skipped on any box.
    ("two_armed_if_else", '''
#[test]
fn t() {
    if native_build_requires_oracle() {
        assert!(oracle_install().is_err());
    } else {
        assert!(oracle_install().is_ok());
    }
}
'''),
    # A `continue` in a loop is not an early exit from the test.
    ("loop_continue", '''
#[test]
fn t() {
    for c in cases() {
        if !c.enabled() { continue; }
        assert!(c.check());
    }
    assert!(true);
}
'''),
]

MUST_CATCH_INDIRECT = [
    ("helper_wrapped_guard", '''
fn skip_no_lean() -> bool {
    !lean_available()
}
#[test]
fn t() {
    if skip_no_lean() { return; }
    assert!(the_verified_thing());
}
'''),
    ("wrapped_if_no_return", '''
#[test]
fn t() {
    if lean_available() {
        assert!(the_verified_thing());
    }
}
'''),
]

MUST_BE_DEMANDED = [
    ("armable_demand", '''
#[test]
fn t() {
    if !dregg_lean_ffi::demand_lean(dregg_lean_ffi::lean_available(), "executor") {
        return;
    }
    assert!(verified_thing());
}
'''),
]


def verdicts_for(src: str) -> list[str]:
    f, _ = scan_file(Path("selftest/src/lib.rs"), src)
    return [x.verdict for x in f]


def self_test() -> int:
    bad = 0
    for name, src in MUST_CATCH:
        v = verdicts_for(src)
        if "SILENT" not in v:
            print(f"  self-test MISS  (must catch) {name}  -> {v}")
            bad += 1
        else:
            print(f"  self-test caught             {name}")
    for name, src in MUST_NOT_CATCH:
        v = verdicts_for(src)
        if any(x in ("SILENT", "DEMANDED") for x in v):
            print(f"  self-test FALSE POSITIVE     {name}  -> {v}")
            bad += 1
        else:
            print(f"  self-test quiet on           {name}")
    for name, src in MUST_CATCH_INDIRECT:
        v = verdicts_for(src)
        if "SILENT" not in v:
            print(f"  self-test MISS  (indirect)   {name}  -> {v}")
            bad += 1
        else:
            print(f"  self-test caught (indirect)  {name}")
    for name, src in MUST_BE_DEMANDED:
        v = verdicts_for(src)
        if "DEMANDED" not in v:
            print(f"  self-test MISCLASSIFIED      {name}  -> {v} (wanted DEMANDED)")
            bad += 1
        else:
            print(f"  self-test classified         {name} as DEMANDED")

    # ── the FLOORS must be shown to BITE ───────────────────────────────────────────
    # `MIN_TESTS`/`MIN_GUARDED` exist because "zero silent skips" is a NEGATIVE claim that
    # a blind reader satisfies perfectly. This gate's OWN first cut proved the point: one
    # off-by-one in `find_body` made it report 0 findings across 20 000 tests, and the
    # headline read clean. So the floors are exercised here, not merely declared.
    _, seen = scan_file(Path("x/src/lib.rs"), MUST_CATCH[0][1])
    if seen != 1:
        print(f"  self-test: test-fn counter is wrong ({seen} != 1) — the floor cannot bite")
        bad += 1
    else:
        print("  self-test counts test fns      (MIN_TESTS floor has something to measure)")

    # A reader that has gone blind reports zero of BOTH populations; both floors must
    # reject that, and both must accept the measured tree.
    if not (0 < MIN_TESTS and 0 < MIN_GUARDED):
        print("  self-test: a floor is <= 0 and therefore unfalsifiable")
        bad += 1
    for name, pop, floor in (("MIN_TESTS", 0, MIN_TESTS), ("MIN_GUARDED", 0, MIN_GUARDED)):
        if not pop < floor:
            print(f"  self-test: {name} does not reject a blind reader (0 >= {floor})")
            bad += 1
        else:
            print(f"  self-test floor bites          {name}: a 0-population read FAILS (floor {floor})")

    # And the blanker must still be reachable — this gate borrows it rather than
    # re-growing it, so a broken import would silently disarm the whole scan.
    if pc.strip_noise('// verify_x()\nlet a = verify_x();') .strip() != "let a = verify_x();":
        print("  self-test: the borrowed Rust blanker is not blanking comments")
        bad += 1
    else:
        print("  self-test blanker live         (strip_noise removes prose, keeps code)")

    print()
    if bad:
        print(f"SELF-TEST FAILED: {bad} case(s)")
        return 1
    print(
        f"SELF-TEST PASSED: {len(MUST_CATCH)} direct + {len(MUST_CATCH_INDIRECT)} indirect caught, "
        f"{len(MUST_NOT_CATCH)} correctly quiet, {len(MUST_BE_DEMANDED)} classified DEMANDED"
    )
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--by-crate", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--bless", action="store_true")
    ap.add_argument("--verdict", default=None, help="filter --report to one verdict")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    findings, total_tests = sweep()
    guarded = [f for f in findings if f.verdict != "ASSERTED"]
    silent = [f for f in findings if f.verdict == "SILENT"]
    demanded = [f for f in findings if f.verdict == "DEMANDED"]
    inverse = [f for f in findings if f.verdict == "INVERSE"]
    reentrant = [f for f in findings if f.verdict == "REENTRANT"]

    if args.report:
        rows = findings if not args.verdict else [f for f in findings if f.verdict == args.verdict]
        for f in sorted(rows, key=lambda f: (f.verdict, str(f.rel), f.line)):
            print(f"{f.verdict:9} {f.rel}:{f.line}\t{f.fn_name}\t[{f.shape}]")
        print(
            f"\n{total_tests} test fns scanned; {len(silent)} SILENT, {len(demanded)} DEMANDED, "
            f"{len(inverse)} INVERSE, {len(reentrant)} REENTRANT, "
            f"{len(findings) - len(guarded)} ASSERTED"
        )
        return 0

    if args.by_crate:
        for verdict in ("SILENT", "DEMANDED", "INVERSE", "REENTRANT"):
            rows = [f for f in findings if f.verdict == verdict]
            print(f"══ {verdict} ({len(rows)}) ══")
            print("  by crate:")
            for crate, n in Counter(f.crate for f in rows).most_common():
                print(f"    {n:4}  {crate}")
            print("  by guard shape:")
            for shape, n in Counter(f.shape for f in rows).most_common():
                print(f"    {n:4}  {shape}")
            print()
        print(f"{total_tests} test fns scanned")
        return 0

    if args.bless:
        # Only the NAMED RESIDUALS. `DEMANDED` needs no baseline (it panics by default
        # now), and blessing a `SILENT` row would be the gate absolving the disease it
        # exists to find.
        rows = inverse + reentrant
        write_baseline(rows)
        print(f"blessed {len(rows)} residual rows into {BASELINE.relative_to(REPO)}")
        if silent:
            print(f"⚠ {len(silent)} SILENT row(s) NOT blessed — those are the disease, not a residual.")
        return 0

    # ── the floors: a broken reader must not read clean ────────────────────────────
    if total_tests < MIN_TESTS:
        print(
            f"FAIL: scanned only {total_tests} test fns, floor is {MIN_TESTS}. The reader is\n"
            "      not parsing this tree's Rust — fix it or lower the floor in this commit\n"
            "      and say why."
        )
        return 1
    if len(guarded) < MIN_GUARDED:
        print(
            f"FAIL: found only {len(guarded)} guard-shaped early returns, floor is "
            f"{MIN_GUARDED}.\n"
            "      The guard classifier has gone blind; a clean headline here would be\n"
            "      the instrument, not the tree."
        )
        return 1

    # ── THE RATCHET ────────────────────────────────────────────────────────────────
    # SILENT is ZERO TOLERANCE, because the tree is AT zero as of 2026-07-27 and the
    # only way back is a new one. INVERSE and REENTRANT are named residuals with their
    # own (different) fixes, so they are baselined rather than forbidden — but a NEW
    # one still has to be looked at and recorded, never absorbed silently.
    known = read_baseline()
    residual_fresh = [f for f in (inverse + reentrant) if f.key() not in known]

    if not silent and not residual_fresh:
        print(
            f"check-silent-skip: OK — {total_tests} test fns scanned, ZERO tests that report "
            f"`ok` without exercising their subject.\n"
            f"  {len(demanded)} route through `demand_lean`, which PANICS by default "
            f"(DREGG_TEST_ALLOW_MISSING_LEAN=1 to opt out, loudly).\n"
            f"  {len(inverse)} INVERSE + {len(reentrant)} REENTRANT are baselined residuals — "
            f"see baseline/silent-skip.tsv."
        )
        return 0

    if silent:
        print(
            f"check-silent-skip: FAIL — {len(silent)} test(s) can return WITHOUT exercising "
            "their subject, and report `ok`:\n"
        )
        for f in sorted(silent, key=lambda f: (str(f.rel), f.line)):
            print(f"  {f.rel}:{f.line}  fn {f.fn_name}()   guard: {f.shape}")
        print(
            "\n`libtest` has exactly two runtime outcomes, and `ok` is one of them — there is no\n"
            "runtime skip. So a test that discovers at run time that it cannot do its job has to\n"
            "pick one of these, and `return` is not on the list:\n"
            "\n"
            "  * PANIC when the fixture SHOULD be there. For anything Lean-archive-shaped, route\n"
            "    the probe through `dregg_lean_ffi::demand_lean(available, \"what\")` — armed by\n"
            "    default, with `DREGG_TEST_ALLOW_MISSING_LEAN=1` as the visible opt-out. One choke\n"
            "    point for the whole verified estate.\n"
            "  * `#[ignore = \"…why, and the exact command to run it…\"]` when the environment\n"
            "    legitimately may lack it (a GPU, a live homeserver, a funded devnet keypair).\n"
            "    `ignored` is a true statement; `ok` is not. Move the env probe to a hard assert\n"
            "    underneath so `--ignored` without the env fails instead of passing hollow.\n"
            "  * `#[cfg_attr(not(feature = \"…\"), ignore = \"…\")]` when a cargo feature decides\n"
            "    it — compile-time, so the harness prints `ignored` rather than discovering it.\n"
        )

    if residual_fresh:
        print(
            f"\ncheck-silent-skip: {len(residual_fresh)} NEW residual row(s) not in the baseline:\n"
        )
        for f in sorted(residual_fresh, key=lambda f: (str(f.rel), f.line)):
            print(f"  {f.verdict:9} {f.rel}:{f.line}  fn {f.fn_name}()   guard: {f.shape}")
        print(
            "\n  INVERSE   the test's subject IS the fixture's absence, so it skips when the\n"
            "            fixture is PRESENT. Demanding availability is backwards for it; the\n"
            "            real fix is injecting unavailability instead of reading the ambient\n"
            "            world. Record it here only once you have confirmed that is the shape.\n"
            "  REENTRANT one half of a two-process test — the parent re-execs the binary with\n"
            "            `--exact <fn>` and a marker env var. The assertions DO happen, in the\n"
            "            child. Residual: the worker still prints `ok` in the parent process.\n"
            "\nIf you have established the classification, record it:\n"
            "    scripts/check-silent-skip.py --bless"
        )
    return 1


if __name__ == "__main__":
    sys.exit(main())
