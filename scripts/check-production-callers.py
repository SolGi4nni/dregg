#!/usr/bin/env python3
"""check-production-callers.py — a public function whose ONLY callers are tests,
and one whose callers do not exist at all.

═══ THE THEATRE CLASS ═════════════════════════════════════════════════════════════
Every "silence" sweep in this repo so far has looked for something MISSING — a file
rustc never opens, a target no workflow can run, a doc reference that does not
resolve. This looks for something PRESENT and inert: a function that is written,
documented, exported, and, on the path that ships, never called.

The instance that produced this script is `dregg_circuit::effect_vm::verify_balance_
limb_pis`. It is the executor-side range precondition under Constraint Group 6 — the
group binds `NET_DELTA = FINAL - INIT` over BabyBear, which out-of-width limbs
satisfy just as happily by modular wrap, so the delta constraint is only as sound as
that precondition. It was defined in `effect_vm::verify`, re-exported from
`effect_vm` AND again from the crate root, its doc comment said "verifiers MUST call
this", and it was invoked by NO production path and NO test. Two re-exports and an
imperative doc comment, and the count of things that ran it was zero.

There is no diagnostic for this anywhere. It compiles (it is `pub`, so it is not
dead code). It has no failing test (it has no test). It reads, in review, exactly
like a check that is happening. **A function nobody calls is indistinguishable from
a function that always passes** — the same shape as the dark-target class, one layer
up: there the guard could not run, here nothing asks it to.

Two populations, and they fail differently:

  UNCALLED   zero call sites in the whole tree, tests included. Nothing has ever
             executed it. Whatever it asserts is asserted by nobody.
  THEATRE    call sites exist and EVERY ONE of them is test code. The function runs
             daily, goes green daily, and does not run in production. This is worse
             than UNCALLED for review purposes: the green is real, and it is
             evidence about the test, not about the deployment.

═══ WHY THIS IS A RATCHET AND NOT A THRESHOLD ═════════════════════════════════════
A public function in a library crate legitimately has no in-tree caller — that is
what a library IS. So the absolute count is not a defect count and a "must be zero"
gate here would be a lie that gets suppressed within a day. What is actionable is
the DELTA: a symbol that JOINS either population is a symbol that was just written
without a caller, or just lost its last production caller, and that is the moment
someone can still remember why.

So `baseline/production-callers.tsv` records the known population and this check goes
red BOTH WAYS — on an addition AND on a stale row. `--bless` rewrites the baseline.

  FRESH   a guard in the population with no baseline row. Just written without a
          caller, or just lost its last production caller.
  STALE   a baseline row whose finding is GONE — the function acquired a production
          caller, was deleted, was renamed, or moved to another file. The row now
          asserts a hole that is closed, and every later reader of this file trusts it.

⚠ The stale arm is not decoration, and its absence was measured on 2026-07-27: this
check was ADDITIONS-ONLY, so a row could be wired up or deleted and the baseline would
keep carrying it forever, indistinguishable from a live finding. The `verify_balance_
limb_pis` row that this script was WRITTEN for would have sat here permanently after
`687e70504` wired it. A ratchet that only turns one way is a ledger, not a ratchet.

═══ THE KEY ═══════════════════════════════════════════════════════════════════════
A row is keyed on `(kind, name, definition_file)` — the file WITHOUT its line number,
because line numbers drift on every unrelated edit above the definition and a key that
churns is a key nobody keeps honest.

The key USED to be `(kind, name)`, name-only, and one row per NAME (`sites[0]`, the
first definition found in path order). Two consequences, both silent:
  * a second, freshly-written uncalled `verify_thing` in ANOTHER crate was absorbed by
    the existing row and reported nothing;
  * a row could not say WHICH crate it was about, so a mover looked like a no-op.
Rows are now per DEFINITION SITE, so a same-named guard in a new crate is a new row and
therefore red.

⚠ RESIDUAL, stated, WITH A FOUND INSTANCE: the CALLER COUNT is still name-keyed (see
"WHAT THIS CANNOT SEE" — this is textual, it does not resolve imports). So if `foo` in
crate A has a production caller, an uncalled `foo` in crate B is still invisible: the
merged count is `prod > 0` and neither site is reported. Per-site rows fix same-name
ABSORPTION of a REPORTED row, not same-name MASKING of an UNREPORTED one.

The instance, found 2026-07-27 while fixing this: `verify_fold_chain` was defined TWICE —
`dregg_commit::fold` (real, many callers) and `dregg_bridge::present` (returned `false`
for every input, zero callers anywhere). `dregg_commit`'s callers absorbed both, so the
bridge one never appeared in any population and was never baselined. It has been deleted.

Measured, so the size of the blind spot is on record rather than guessed: 50 GUARD names
have more than one definition site AND a merged `prod > 0`; expanded per site that is 186
rows. Baselining all 186 was considered and rejected — this file's own thesis is that a
gate nobody reads is not a gate, and ~180 rows of `is_valid` / `is_verified` /
`is_well_formed` across unrelated crates is that wall. Closing it properly needs real
path resolution, not more rows.

═══ WHAT THIS CANNOT SEE — stated, not hidden ═════════════════════════════════════
  * DYNAMIC calls. A symbol reached only as a function pointer, through a trait
    object, or by a macro that pastes its name is invisible here. It will read as
    UNCALLED and be wrong about it.
  * FFI and re-export consumers. `#[export]`/`extern "C"` symbols are called from
    outside this tree entirely, as are symbols consumed by the excluded workspaces
    (`discord-bot`, `dreggnet-market`) and by downstream repos. These are skipped by
    attribute where detectable and belong in the baseline otherwise.
  * It is TEXTUAL. Call sites are matched on shape (`name(`, `::name`, `.name(`)
    after comments and string literals are stripped. It does not resolve paths, so
    two crates with a same-named function share a verdict. `sg` would resolve the
    AST but not the imports either, and would cost a process per symbol.
  * It cannot tell a CORRECT production caller from a wrong one. It counts.

Usage:
    scripts/check-production-callers.py              # ratchet against the baseline
    scripts/check-production-callers.py --report     # print the whole population
    scripts/check-production-callers.py --bless      # rewrite the baseline
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "baseline" / "production-callers.tsv"

# Directories that are not this repo's own source.
SKIP_DIR_PARTS = {
    ".git", "target", ".lake", "node_modules", "vendor", ".claude",
    ".cargo", "dist", ".venv", "__pycache__",
}

# A file is TEST CODE in its entirety when it lives here.
TEST_DIR_NAMES = {"tests", "benches"}

# Symbols whose callers are structurally outside this tree.
FFI_MARKERS = ("#[no_mangle]", 'extern "C"', "#[unsafe(no_mangle)]")


def is_skipped(path: Path) -> bool:
    return any(part in SKIP_DIR_PARTS for part in path.parts)


def rust_files() -> list[Path]:
    out = []
    for path in ROOT.rglob("*.rs"):
        if not is_skipped(path.relative_to(ROOT)):
            out.append(path)
    out.sort()
    return out


def strip_noise(text: str) -> str:
    """Blank out comments, string literals and char literals, PRESERVING offsets.

    Call-site counting must not be inflated by prose — this repo's doc comments name
    functions constantly (`verify_slot_caveat_manifest` appears in eleven of them),
    and a census that counts those reports a wired symbol that is not wired.

    ⚠ This is a real scanner and not a pair of regexes, because the regex version was
    WRONG IN THE DIRECTION THAT HIDES THINGS. Stripping `/\\*.*?\\*/` first means a
    `/*` appearing inside a LINE comment (a glob, a path, a bit of ASCII art — this
    tree is full of them) opens a block comment that runs to the next `*/` anywhere
    later in the file, blanking everything between. Measured on the first cut: both
    freshly-added `verify_balance_limb_pis` call sites vanished and the symbol was
    reported UNCALLED minutes after being wired. An under-reporting census is worse
    than none: it is a clean bill of health issued by an instrument that was not
    looking.

    Removed spans become spaces rather than disappearing, so every offset this
    function returns still indexes the original text.
    """
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            depth = 0  # Rust block comments nest.
            while i < n:
                if text.startswith("/*", i):
                    depth += 1
                    out[i] = out[i + 1] = " "
                    i += 2
                elif text.startswith("*/", i):
                    depth -= 1
                    out[i] = out[i + 1] = " "
                    i += 2
                    if depth == 0:
                        break
                else:
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
        elif c == "r" and (m := re.match(r'r(#*)"', text[i:])):
            hashes = m.group(1)
            close = text.find('"' + hashes, i + len(m.group(0)))
            end = n if close == -1 else close + 1 + len(hashes)
            for j in range(i, end):
                if text[j] != "\n":
                    out[j] = " "
            i = end
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                if text[k] != "\n":
                    out[k] = " "
            i = j + 1
        elif c == "'" and i + 2 < n and (text[i + 1] != "\\" and text[i + 2] == "'"):
            # A char literal — `'{'` and `'}'` would otherwise unbalance brace matching.
            out[i] = out[i + 1] = out[i + 2] = " "
            i += 3
        else:
            i += 1
    return "".join(out)


CFG_TEST = re.compile(r"#\[cfg\(test\)\]")
TEST_ATTR = re.compile(r"#\[(?:\w+::)?test\b|#\[(?:tokio|async_std)::test\b|proptest!")


def test_regions(text: str) -> list[tuple[int, int]]:
    """Character spans of `#[cfg(test)] mod … { … }` blocks, by brace matching.

    Anything inside one is test code even though the file is a `src/` file. This is
    where the THEATRE population usually hides: an in-module test block calling a
    function the production half of the very same file never calls.
    """
    spans: list[tuple[int, int]] = []
    for m in CFG_TEST.finditer(text):
        brace = text.find("{", m.end())
        if brace == -1:
            continue
        # Only follow a `mod` (or an item) that opens a block reasonably close by.
        if "\n" in text[m.end():brace] and text[m.end():brace].count("\n") > 3:
            continue
        depth, i = 0, brace
        while i < len(text):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
                if depth == 0:
                    spans.append((m.start(), i))
                    break
            i += 1
    return spans


def in_spans(pos: int, spans: list[tuple[int, int]]) -> bool:
    return any(lo <= pos <= hi for lo, hi in spans)


PUB_FN = re.compile(r"^\s*pub(?:\s*\([^)]*\))?\s+(?:async\s+)?(?:unsafe\s+)?(?:extern\s+\"[^\"]*\"\s+)?fn\s+([a-z_][a-z0-9_]*)\s*[(<]", re.M)


def collect_definitions(files: list[Path]) -> dict[str, list[tuple[Path, int]]]:
    """Every `pub fn` defined under a crate `src/` directory."""
    defs: dict[str, list[tuple[Path, int]]] = {}
    for path in files:
        rel = path.relative_to(ROOT)
        if "src" not in rel.parts:
            continue
        if any(p in TEST_DIR_NAMES for p in rel.parts):
            continue
        raw = path.read_text(encoding="utf-8", errors="replace")
        if any(marker in raw for marker in FFI_MARKERS):
            # Cheap and deliberately whole-file: an FFI file's exports are called
            # from outside the tree, and per-symbol attribution here would be a
            # guess. Better to skip the file than to report a confident wrong row.
            continue
        text = strip_noise(raw)
        spans = test_regions(text)
        for m in PUB_FN.finditer(text):
            if in_spans(m.start(), spans):
                continue
            line = text.count("\n", 0, m.start()) + 1
            defs.setdefault(m.group(1), []).append((rel, line))
    return defs


def count_callers(files: list[Path], names: set[str]) -> dict[str, tuple[int, int]]:
    """(production_calls, test_calls) per name, excluding the definition sites."""
    counts = {n: [0, 0] for n in names}
    # ONE generic call-shape scan per file, filtered against the name set — not an
    # alternation over every known name. The alternation is the obvious spelling and
    # it is quadratic in practice (thousands of branches re-tried at every position);
    # the first cut of this script did not finish.
    pattern = re.compile(r"(?<![A-Za-z0-9_])([a-z_][a-z0-9_]*)\s*(?=\()")
    for path in files:
        rel = path.relative_to(ROOT)
        raw = path.read_text(encoding="utf-8", errors="replace")
        text = strip_noise(raw)
        file_is_test = any(p in TEST_DIR_NAMES for p in rel.parts)
        spans = [] if file_is_test else test_regions(text)
        def_lines = {m.start() for m in PUB_FN.finditer(text)}
        for m in pattern.finditer(text):
            name = m.group(1)
            if name not in counts:
                continue
            # The definition's own `fn name(` is not a call.
            if text.rfind("fn ", max(0, m.start() - 4), m.start()) != -1:
                continue
            if file_is_test or in_spans(m.start(), spans) or TEST_ATTR.search(text[max(0, m.start() - 400):m.start()]):
                counts[name][1] += 1
            else:
                counts[name][0] += 1
    return {k: (v[0], v[1]) for k, v in counts.items()}


# ═══ THE GUARD CLASS ═══════════════════════════════════════════════════════════
# Measured on this tree: 12 785 `pub fn`s, of which ~4 800 have no production caller.
# That is not 4 800 defects — a library's public surface is SUPPOSED to have callers
# it cannot see, and a gate over that number is a wall nobody reads, which is the
# failure mode this repo keeps paying for (a report-only linter is not a gate).
#
# So the ratchet runs over the subset where "nobody calls it" is a CLAIM ABOUT
# SAFETY rather than about API shape: functions that DECIDE something. A function
# named `verify_*` / `check_*` / `*_admits` is not offering a capability, it is
# asserting that something was checked — and if nothing calls it, that assertion is
# made by nobody while reading, in review, exactly like a check that happens.
#
# `verify_balance_limb_pis` was in this class, and it is the whole reason for the
# script. The wider population stays available under `--report`.
GUARD_PREFIXES = (
    "verify_", "check_", "validate_", "assert_", "enforce_", "ensure_",
    "reject_", "refuse_", "require_", "audit_", "must_",
)
GUARD_SUFFIXES = (
    "_admits", "_accepts", "_is_valid", "_valid", "_verified", "_authorized",
    "_permitted", "_conserves", "_well_formed",
)


def is_guard(name: str) -> bool:
    return name.startswith(GUARD_PREFIXES) or name.endswith(GUARD_SUFFIXES)


def classify(defs, counts) -> list[tuple[str, str, str, int, int]]:
    """One row PER DEFINITION SITE: `(kind, name, file, line, test_call_sites)`.

    Per-site, not per-name: a second same-named uncalled guard in another crate must be a
    NEW row (and therefore red), not absorbed by the existing one. Sites in the same file
    collapse to the earliest line — one `pub fn` per (name, file) is the norm, and a
    `cfg`-duplicated pair is one finding, not two.
    """
    rows = []
    for name, sites in sorted(defs.items()):
        prod, test = counts.get(name, (0, 0))
        # ⚑ A NAME'S CALLERS DO NOT CLEAR EVERY DEFINITION OF THAT NAME.
        #
        # `460727e9f` moved the ratchet's DEFINITION key to `(kind, name, definition_file)` and left
        # the caller counts keyed by bare NAME. So when two files define the same function and only
        # one of them is called, `prod > 0` silently cleared BOTH — the uncalled sibling vanished
        # from the report entirely. Measured: it was hiding two guards.
        #
        # ⚠ The counts CANNOT be split per definition without name resolution: a bare `foo()` call
        # site does not say which `foo` it reached, and this scanner is deliberately a call-SHAPE
        # scan (the alternation-over-every-name spelling is quadratic and the first cut never
        # finished). So the fix is not "count better" — it is to stop treating an ambiguous clear as
        # a definite one.
        #
        # Narrow rule: a production caller clears the name only when the name has exactly ONE
        # definition site. With several, `prod > 0` proves only that SOME one of them is reached, so
        # the rest stay in the report, flagged as ambiguous rather than silently dropped or falsely
        # accused.
        distinct_files = {str(path) for path, _ in sites}
        if prod > 0 and len(distinct_files) == 1:
            continue
        if prod > 0:
            # Several definitions share this name and something calls it. Which one is unknowable
            # here, so report them as AMBIGUOUS — a reader can resolve it in seconds and the gate
            # stops asserting a clearance it cannot establish.
            for path in sorted(distinct_files):
                earliest_line = min(l for pth, l in sites if str(pth) == path)
                rows.append(("AMBIGUOUS", name, path, earliest_line, test))
            continue
        kind = "THEATRE" if test > 0 else "UNCALLED"
        earliest: dict[str, int] = {}
        for path, line in sites:
            key = str(path)
            earliest[key] = min(line, earliest.get(key, line))
        for path in sorted(earliest):
            rows.append((kind, name, path, earliest[path], test))
    return rows


def row_key(row) -> tuple[str, str, str]:
    """`(kind, name, definition_file)` — see THE KEY in the header. The LINE is
    deliberately not part of it: it drifts on every edit above the definition."""
    return (row[0], row[1], row[2])


class BaselineFormatError(Exception):
    pass


def read_baseline() -> set[tuple[str, str, str]]:
    if not BASELINE.exists():
        return set()
    return parse_baseline(BASELINE.read_text())


def parse_baseline(text: str) -> set[tuple[str, str, str]]:
    out = set()
    for lineno, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 3:
            raise BaselineFormatError(
                f"{BASELINE.name}:{lineno}: expected at least 3 tab-separated fields "
                f"(kind, name, definition_file), got {len(parts)}"
            )
        if ":" in parts[2]:
            # The retired name-only-key format wrote `path:line` in field 3. REFUSE it
            # rather than reinterpret: silently treating `a.rs:60` as a file name would
            # make every row stale AND every finding fresh, which reads as a catastrophe
            # instead of as a format change.
            raise BaselineFormatError(
                f"{BASELINE.name}:{lineno}: field 3 is `{parts[2]}` — a `path:line` from the "
                "RETIRED name-only-key baseline format. The key is now "
                "(kind, name, definition_file) with the line in its own column. "
                "Re-emit with: scripts/check-production-callers.py --bless"
            )
        out.add((parts[0], parts[1], parts[2]))
    return out


def write_baseline(rows) -> None:
    BASELINE.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# production-callers.tsv — the KNOWN population of `pub fn`s with no production caller.",
        "# Written by scripts/check-production-callers.py --bless. See that file's header for what",
        "# UNCALLED and THEATRE mean, for what this census cannot see, and for the row KEY.",
        "#",
        "# A row is keyed on (kind, name, definition_file) — the LINE column is informational and",
        "# is not part of the key. The check goes red BOTH ways: a guard with no row is FRESH, a",
        "# row with no guard is STALE (it acquired a caller, or was deleted/renamed/moved).",
        "#",
        "# kind\tname\tdefinition_file\tdefinition_line\ttest_call_sites",
    ]
    for kind, name, path, line, test in rows:
        lines.append(f"{kind}\t{name}\t{path}\t{line}\t{test}")
    BASELINE.write_text("\n".join(lines) + "\n")


SELF_TEST_SOURCE = '''
// A line comment mentioning a glob like docs/*.md and a path a/*/b — this is the
// trap: read as a block-comment opener, everything to the next */ disappears.
/// Doc prose naming verify_the_thing() without calling it.
pub fn verify_the_thing(x: u32) -> bool { x > 0 }
pub fn unwired_guard(x: u32) -> bool { x > 0 }
pub fn caller() -> bool { verify_the_thing(1) }
#[cfg(test)]
mod tests {
    #[test]
    fn t() { assert!(super::unwired_guard(1)); }
}
'''


def self_test() -> int:
    """Prove this check can go RED, and that its scanner still sees a call after the
    `/*`-inside-a-line-comment trap that made the first cut under-report.

    A negative assertion — "no new uncalled guards" — passes just as happily when the
    reader is broken, and this one WAS broken in exactly that direction. So the pairing
    is not decoration.
    """
    text = strip_noise(SELF_TEST_SOURCE)
    spans = test_regions(text)
    failures = []

    if "verify_the_thing(1)" not in text:
        failures.append(
            "the scanner LOST a real call site — a `/*` inside a line comment is eating "
            "source again, which is the under-reporting bug this check was blind to"
        )
    if "Doc prose naming" in text:
        failures.append("doc prose survived stripping; call counts will be inflated by comments")

    call_positions = [i for i in range(len(text)) if text.startswith("verify_the_thing(", i)]
    production_calls = [p for p in call_positions if not in_spans(p, spans)]
    if not production_calls:
        failures.append("a production call site was misclassified as test code")

    test_calls = [i for i in range(len(text)) if text.startswith("unwired_guard(", i)]
    if not any(in_spans(p, spans) for p in test_calls):
        failures.append(
            "a call inside `#[cfg(test)] mod` was NOT recognised as test code — the THEATRE "
            "class cannot be detected"
        )

    if not is_guard("verify_the_thing") or is_guard("caller"):
        failures.append("the guard-class predicate does not separate deciders from ordinary fns")

    # ── THE RATCHET, BOTH DIRECTIONS. Each arm is driven red on purpose; a negative
    #    assertion ("nothing new, nothing stale") passes just as happily on a broken reader.
    baseline = {("UNCALLED", "verify_baselined", "kept/src/lib.rs")}

    # ARM 1 — FRESH: an unbaselined uncalled guard must register.
    guards = [
        ("UNCALLED", "verify_baselined", "kept/src/lib.rs", 1, 0),
        ("UNCALLED", "verify_a_thing_nobody_baselined", "x/src/lib.rs", 1, 0),
    ]
    fresh = [r for r in guards if is_guard(r[1]) and row_key(r) not in baseline]
    if [r[1] for r in fresh] != ["verify_a_thing_nobody_baselined"]:
        failures.append(
            "the FRESH arm did not isolate the unbaselined guard "
            f"(got {[r[1] for r in fresh]})"
        )

    # ARM 2 — STALE: a baseline row whose guard is no longer in the population must
    # register. This arm did not exist until 2026-07-27; the check was additions-only, so a
    # row survived being wired up or deleted and kept asserting a hole that was closed.
    wired_up = [("UNCALLED", "verify_a_thing_nobody_baselined", "x/src/lib.rs", 1, 0)]
    stale = baseline - {row_key(r) for r in wired_up}
    if {k[1] for k in stale} != {"verify_baselined"}:
        failures.append(
            "the STALE arm did not register a baseline row whose function left the "
            f"population (got {sorted(k[1] for k in stale)}) — the ratchet only turns one way"
        )
    if not (baseline - {row_key(r) for r in guards}) == set():
        failures.append("a row still in the population was wrongly reported STALE")

    # ARM 3 — THE KEY MUST NOT COLLIDE. Two same-named uncalled guards in different crates
    # are TWO findings. Under the retired name-only key the second was absorbed silently.
    dup_defs = {
        "verify_same_name": [
            (Path("crate_a/src/lib.rs"), 10),
            (Path("crate_b/src/lib.rs"), 20),
        ]
    }
    dup_rows = classify(dup_defs, {"verify_same_name": (0, 0)})
    if len({row_key(r) for r in dup_rows}) != 2:
        failures.append(
            "two same-named guards in different crates collapsed to one key — a freshly "
            "written uncalled decider in a new crate would be absorbed by the existing row"
        )
    if [r for r in dup_rows if row_key(r) not in {row_key(dup_rows[0])}] == []:
        failures.append("the per-site expansion produced no second row at all")

    # ARM 4 — the RETIRED name-only-key baseline must REFUSE to load, not be reinterpreted.
    try:
        parse_baseline("UNCALLED\tverify_x\tcrate/src/lib.rs:60\t0\n")
    except BaselineFormatError:
        pass
    else:
        failures.append(
            "a retired-format baseline row (`path:line` in field 3) loaded silently — every "
            "row would read STALE and every finding FRESH, a format change disguised as a fire"
        )
    if parse_baseline(
        "# comment\nUNCALLED\tverify_x\tcrate/src/lib.rs\t60\t0\n"
    ) != {("UNCALLED", "verify_x", "crate/src/lib.rs")}:
        failures.append("the current baseline format does not round-trip through the parser")

    if failures:
        print("check-production-callers --self-test: FAIL")
        for f in failures:
            print(f"  * {f}")
        return 1
    print("check-production-callers --self-test: OK — the scanner sees calls through the "
          "comment trap, separates test from production call sites, an unbaselined guard "
          "registers FRESH, a baseline row that left the population registers STALE, two "
          "same-named guards in different crates key apart, and a retired-format baseline "
          "refuses to load.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report", action="store_true", help="print the whole population")
    ap.add_argument("--bless", action="store_true", help="rewrite the baseline")
    ap.add_argument("--self-test", action="store_true", help="prove this check can go red")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    files = rust_files()
    defs = collect_definitions(files)
    if not defs:
        print("check-production-callers: found no `pub fn` definitions at all — the census is "
              "not measuring what it claims to. Refusing to report a clean sweep.", file=sys.stderr)
        return 2
    counts = count_callers(files, set(defs))
    rows = classify(defs, counts)

    uncalled = [r for r in rows if r[0] == "UNCALLED"]
    theatre = [r for r in rows if r[0] == "THEATRE"]

    if args.report:
        for kind, name, path, line, test in rows:
            suffix = f"  ({test} test call sites)" if test else ""
            print(f"{kind:9} {name:52} {path}:{line}{suffix}")
        print(f"\n{len(uncalled)} UNCALLED, {len(theatre)} THEATRE, {len(defs)} pub fns scanned")
        return 0

    if args.bless:
        blessed = [r for r in rows if is_guard(r[1])]
        write_baseline(blessed)
        print(f"blessed {len(blessed)} guard rows into {BASELINE.relative_to(ROOT)}")
        return 0

    guards = [r for r in rows if is_guard(r[1])]
    try:
        known = read_baseline()
    except BaselineFormatError as e:
        print(f"check-production-callers: FAIL — {e}", file=sys.stderr)
        return 1

    by_key = {row_key(r): r for r in guards}
    fresh = [r for r in guards if row_key(r) not in known]
    stale = sorted(known - set(by_key))

    if not fresh and not stale:
        print(f"check-production-callers: OK — {len(guards)} uncalled GUARDS, all in the "
              f"baseline, and every baseline row still a live finding. ({len(uncalled)} "
              f"UNCALLED + {len(theatre)} THEATRE overall across {len(defs)} pub fns; "
              f"see --report.)")
        return 0

    print("check-production-callers: FAIL\n")

    if fresh:
        print("FRESH — a function that DECIDES something, with no production caller and no "
              "baseline row:\n")
        for kind, name, path, line, test in fresh:
            if kind == "THEATRE":
                print(f"  THEATRE   {name}\n            {path}:{line}\n"
                      f"            {test} call site(s), every one of them test code. It goes "
                      f"green daily and does not run in production.\n")
            else:
                print(f"  UNCALLED  {name}\n            {path}:{line}\n"
                      f"            no call sites anywhere, tests included.\n")
        print("Wire it up, delete it, or — if its callers are genuinely outside this tree — "
              "record it:")
        print("    scripts/check-production-callers.py --bless\n")

    if stale:
        print("STALE — a baseline row whose finding is GONE. The row asserts a hole that is no "
              "longer there, and the next reader of the baseline believes it:\n")
        for kind, name, path in stale:
            live = [r for r in rows if r[1] == name and r[2] == path]
            if live:
                became = live[0][0]
                why = (f"still uncalled, but now {became}, not {kind} — the call-site population "
                       f"changed shape")
            elif name in defs:
                why = ("the function now HAS a production caller, or moved to another file "
                       "(it is still defined in this tree)")
            else:
                why = "the function is gone from this tree entirely (deleted or renamed)"
            print(f"  {kind:9} {name}\n            {path}\n            {why}\n")
        print("Drop the row — removing one is always allowed:")
        print("    scripts/check-production-callers.py --bless")
    return 1


if __name__ == "__main__":
    sys.exit(main())
