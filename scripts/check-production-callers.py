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

So `baseline/production-callers.tsv` records the known population and this check
goes red on additions. Removing a row (wiring a symbol up, or deleting it) is always
allowed and the baseline is rewritten by `--bless`.

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


def classify(defs, counts) -> list[tuple[str, str, str, int]]:
    rows = []
    for name, sites in sorted(defs.items()):
        prod, test = counts.get(name, (0, 0))
        if prod > 0:
            continue
        kind = "THEATRE" if test > 0 else "UNCALLED"
        where = f"{sites[0][0]}:{sites[0][1]}"
        rows.append((kind, name, where, test))
    return rows


def read_baseline() -> set[tuple[str, str]]:
    if not BASELINE.exists():
        return set()
    out = set()
    for line in BASELINE.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) >= 2:
            out.add((parts[0], parts[1]))
    return out


def write_baseline(rows) -> None:
    BASELINE.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# production-callers.tsv — the KNOWN population of `pub fn`s with no production caller.",
        "# Written by scripts/check-production-callers.py --bless. See that file's header for what",
        "# UNCALLED and THEATRE mean and for what this census cannot see.",
        "#",
        "# kind\tname\tdefinition\ttest_call_sites",
    ]
    for kind, name, where, test in rows:
        lines.append(f"{kind}\t{name}\t{where}\t{test}")
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

    # And the ratchet itself: an unbaselined guard row must FAIL.
    rows = [("UNCALLED", "verify_a_thing_nobody_baselined", "x/src/lib.rs:1", 0)]
    if not [r for r in rows if is_guard(r[1]) and (r[0], r[1]) not in read_baseline()]:
        failures.append("an unbaselined uncalled guard did not register as a fresh finding")

    if failures:
        print("check-production-callers --self-test: FAIL")
        for f in failures:
            print(f"  * {f}")
        return 1
    print("check-production-callers --self-test: OK — the scanner sees calls through the "
          "comment trap, separates test from production call sites, and an unbaselined "
          "guard registers as red.")
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
        for kind, name, where, test in rows:
            suffix = f"  ({test} test call sites)" if test else ""
            print(f"{kind:9} {name:52} {where}{suffix}")
        print(f"\n{len(uncalled)} UNCALLED, {len(theatre)} THEATRE, {len(defs)} pub fns scanned")
        return 0

    if args.bless:
        blessed = [r for r in rows if is_guard(r[1])]
        write_baseline(blessed)
        print(f"blessed {len(blessed)} guard rows into {BASELINE.relative_to(ROOT)}")
        return 0

    guards = [r for r in rows if is_guard(r[1])]
    known = read_baseline()
    fresh = [r for r in guards if (r[0], r[1]) not in known]
    if not fresh:
        print(f"check-production-callers: OK — {len(guards)} uncalled GUARDS, all in the "
              f"baseline. ({len(uncalled)} UNCALLED + {len(theatre)} THEATRE overall across "
              f"{len(defs)} pub fns; see --report.)")
        return 0

    print("check-production-callers: FAIL — a function that DECIDES something, with no "
          "production caller and no baseline row:\n")
    for kind, name, where, test in fresh:
        if kind == "THEATRE":
            print(f"  THEATRE   {name}\n            {where}\n"
                  f"            {test} call site(s), every one of them test code. It goes green "
                  f"daily and does not run in production.\n")
        else:
            print(f"  UNCALLED  {name}\n            {where}\n"
                  f"            no call sites anywhere, tests included.\n")
    print("Wire it up, delete it, or — if its callers are genuinely outside this tree — record it:")
    print("    scripts/check-production-callers.py --bless")
    return 1


if __name__ == "__main__":
    sys.exit(main())
