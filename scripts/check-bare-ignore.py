#!/usr/bin/env python3
"""check-bare-ignore.py — every `#[ignore]` has to say WHY, and where it can be run.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
An `#[ignore]` with no reason is a test that has been switched off by someone who is
no longer here to be asked. The harness prints it as `ignored`, which is honest, and
then nothing in the tree can tell you whether it is switched off because it takes four
minutes, because it wants a GPU, or because it went red in a hurry one evening. The
last of those is the one worth finding, and it is indistinguishable from the other two
without a reason string.

This repo is, as of 2026-07-27, at ZERO of them: 270 `#[ignore]` attributes, 270
reason strings. The gate exists to keep that number at zero, because the population is
large enough (270 across 224 crates) that a single un-annotated one merges unnoticed.

═══ ⚠ WHY THIS IS NOT `grep -F '#[ignore]'` ═══════════════════════════════════════
Because that reports 177 violations on a tree that has none, and every one is prose.

This tree writes ABOUT its own ignore attributes constantly — in doc comments, in
coverage-gate tables, and (the nastiest form) INSIDE the reason strings themselves:

    redteam/tests/devnet_adversarial.rs:91
      #[ignore = "live devnet red-team: needs DREGG_DEVNET_REDTEAM=1 … Without it this
                  asserts NOTHING — an #[ignore] reports `ignored` (honest), not `ok`
                  (a lie)."]

    circuit/tests/producer_descriptor_coverage_gate.rs:261
      Uncovered("cap-open prove-through #[ignore]d (IR-v2 cap-node lookup handoff)"),

A naive scan calls all 24 rows of that coverage table violations. That is the failure
direction that MATTERS here: a gate crying wolf on 177 phantom rows is a gate that gets
switched off in a week, and then the one real bare `#[ignore]` lands behind it.

So the scan runs over code with comments, string literals and char literals BLANKED —
`scripts/check-production-callers.py::strip_noise`, borrowed rather than re-grown. That
function preserves byte offsets (removed spans become spaces, newlines survive), so
every line number reported here still indexes the original file. It is also already
scarred in the right place: its own docstring records that the regex version let a `/*`
inside a LINE comment open a block comment that ran to the next `*/` and blanked
everything between.

Blanking is what makes the classifier trivial, which is the point:

    #[ignore]                 ->  `#[ignore]`           VIOLATION
    #[ignore = "SLOW: …"]     ->  `#[ignore =        ]` fine — a reason was there

═══ WHAT COUNTS AS A VIOLATION ════════════════════════════════════════════════════
  V1  `#[ignore]`                        — the bare attribute, in any spacing.
  V2  `#[cfg_attr(<pred>, ignore)]`      — the conditional form, equally reasonless.
                                           `ignore = "…"` inside `cfg_attr` is fine.

═══ THE FLOOR ═════════════════════════════════════════════════════════════════════
A gate whose headline is a NEGATIVE assertion ("no bare ones") passes just as happily
when the reader is broken and sees nothing at all. So this also asserts that it FOUND
at least `MIN_IGNORES` attributes. If a refactor legitimately drops the population
below that, lower the floor in the same commit and say why — the number is supposed to
be argued with, not silently satisfied.

Usage:
    scripts/check-bare-ignore.py               # the gate
    scripts/check-bare-ignore.py --report      # the whole population, with reasons
    scripts/check-bare-ignore.py --self-test   # can it go red? (and does it stay
                                               #  quiet on the 177 prose mentions)
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# ── the Rust blanker, borrowed rather than re-grown ────────────────────────────────
# `check-production-callers.py::strip_noise` blanks comments/strings/char literals and
# PRESERVES offsets, and is tested by that gate's own run. A second blanker here would
# be a second thing to be wrong. The hyphen in the filename is why this is importlib.
_PC_PATH = REPO / "scripts" / "check-production-callers.py"
_spec = importlib.util.spec_from_file_location("_pc", _PC_PATH)
if _spec is None or _spec.loader is None:  # pragma: no cover
    sys.exit(f"UNAVAILABLE: cannot load the Rust blanker at {_PC_PATH}")
pc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pc)

# Not this repo's own Rust. `vendor/` IS in scope: those three crates are forks we
# author and edit (`vendor/bulletproofs-r1cs-wgpu` carries four of the attributes).
SKIP_DIR_PARTS = {
    ".git", "target", ".lake", "node_modules", ".claude",
    ".cargo", "dist", ".venv", "__pycache__", "metatheory",
}

# See THE FLOOR above. Population was 270 on 2026-07-27.
MIN_IGNORES = 200

IGNORE_ATTR = re.compile(r"#\s*\[\s*ignore\b")
CFG_ATTR = re.compile(r"#\s*\[\s*cfg_attr\s*\(")


def rust_files() -> list[Path]:
    out = [
        p for p in REPO.rglob("*.rs")
        if not any(part in SKIP_DIR_PARTS for part in p.relative_to(REPO).parts)
    ]
    out.sort()
    return out


def scan(text: str) -> list[dict]:
    """Every `#[ignore]`-family attribute in `text`, classified.

    `text` must ALREADY be blanked by `strip_noise`, so a surviving `"` cannot occur
    and the only thing after `#[ignore` is `]` (bare) or `=` (a reason was present).
    """
    found: list[dict] = []

    for m in IGNORE_ATTR.finditer(text):
        j = m.end()
        while j < len(text) and text[j] in " \t\r\n":
            j += 1
        # `]` closes it with nothing said; `=` means a (now-blanked) reason string.
        found.append({"pos": m.start(), "kind": "ignore",
                      "bare": j < len(text) and text[j] == "]"})

    # V2: `#[cfg_attr(<pred>, ignore)]` — reasonless in the same way. A reasoned
    # `cfg_attr(…, ignore = "…")` blanks to `ignore =` and is accepted.
    for m in CFG_ATTR.finditer(text):
        depth, j = 1, m.end()
        while j < len(text) and depth:
            depth += (text[j] == "(") - (text[j] == ")")
            j += 1
        inner = text[m.end():j - 1]
        for im in re.finditer(r"\bignore\b", inner):
            k = im.end()
            while k < len(inner) and inner[k] in " \t\r\n":
                k += 1
            if k >= len(inner) or inner[k] != "=":
                found.append({"pos": m.start(), "kind": "cfg_attr", "bare": True})

    return found


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def reason_at(raw: str, pos: int) -> str:
    """The reason as WRITTEN, read from the unblanked source, for --report."""
    m = re.compile(r"#\s*\[\s*ignore\s*=\s*(.*?)\]\s*$", re.S).match(raw, pos)
    if not m:
        seg = raw[pos:pos + 400]
        end = seg.find("]")
        return " ".join(seg[:end if end > 0 else 120].split())
    return " ".join(m.group(1).split())[:160]


def sweep() -> tuple[list[tuple[Path, int, str]], list[tuple[Path, int, str]]]:
    violations: list[tuple[Path, int, str]] = []
    population: list[tuple[Path, int, str]] = []
    for path in rust_files():
        try:
            raw = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if "ignore" not in raw:
            continue
        blanked = pc.strip_noise(raw)
        for hit in scan(blanked):
            rel = path.relative_to(REPO)
            row = (rel, line_of(raw, hit["pos"]), hit["kind"])
            population.append(row)
            if hit["bare"]:
                violations.append(row)
    return violations, population


# ═══ SELF-TEST ═════════════════════════════════════════════════════════════════════
# MUST_CATCH is the disease. MUST_NOT_CATCH is every shape that made a naive grep
# report 177 phantoms — each one lifted from the real tree, not invented.
MUST_CATCH = [
    ("plain", '#[test]\n#[ignore]\nfn t() {}'),
    ("spaced", '#[test]\n#[ ignore ]\nfn t() {}'),
    ("cfg_attr", '#[test]\n#[cfg_attr(target_os = "linux", ignore)]\nfn t() {}'),
    ("after_reasoned", '#[ignore = "SLOW: real fold"]\nfn a() {}\n#[ignore]\nfn b() {}'),
]

MUST_NOT_CATCH = [
    ("reasoned", '#[test]\n#[ignore = "SLOW: real recursion fold (~minutes)"]\nfn t() {}'),
    # The nastiest real shape: the reason string TALKS ABOUT `#[ignore]`.
    ("mention_inside_reason",
     '#[ignore = "live devnet red-team: without it this asserts NOTHING '
     '\\u2014 an #[ignore] reports `ignored` (honest), not `ok` (a lie)."]\nfn t() {}'),
    # circuit/tests/producer_descriptor_coverage_gate.rs — 24 rows of this.
    ("mention_in_string",
     'let rows = vec![Uncovered("cap-open prove-through #[ignore]d (IR-v2 handoff)")];'),
    ("mention_in_line_comment",
     '/// The descriptor is parsed, OR a roundtrip exists but is `#[ignore]`d\nfn t() {}'),
    ("mention_in_block_comment",
     '/* a note: this used to be #[ignore] before the fold got fast */\nfn t() {}'),
    ("mention_in_raw_string",
     'const DOC: &str = r##"run the #[ignore] ones with --ignored"##;'),
    # A line comment holding `/*` must not open a block comment that swallows the file.
    ("glob_in_line_comment",
     '// see circuit/tests/*.rs /* not a comment opener\n#[ignore = "GPU: real adapter"]\nfn t() {}'),
    ("multiline_reason",
     '#[ignore = "SLOW, MEASURED: needs a MINTED LEG \\\n            ~108s/leg. RUN AND GREEN."]\nfn t() {}'),
    ("cfg_attr_reasoned",
     '#[cfg_attr(miri, ignore = "miri cannot run the FFI")]\nfn t() {}'),
]


def self_test() -> int:
    bad = 0
    for name, src in MUST_CATCH:
        hits = [h for h in scan(pc.strip_noise(src)) if h["bare"]]
        if not hits:
            print(f"  self-test MISS  (must catch) {name}")
            bad += 1
        else:
            print(f"  self-test caught             {name}")
    for name, src in MUST_NOT_CATCH:
        hits = [h for h in scan(pc.strip_noise(src)) if h["bare"]]
        if hits:
            print(f"  self-test FALSE POSITIVE     {name}")
            bad += 1
        else:
            print(f"  self-test quiet on           {name}")

    # The floor has to be able to bite too.
    if len(scan(pc.strip_noise(MUST_CATCH[0][1]))) != 1:
        print("  self-test: population count is wrong on a one-attribute input")
        bad += 1

    print()
    if bad:
        print(f"SELF-TEST FAILED: {bad} case(s)")
        return 1
    print(f"SELF-TEST PASSED: {len(MUST_CATCH)} caught, {len(MUST_NOT_CATCH)} correctly quiet")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--report", action="store_true", help="print the whole population")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    violations, population = sweep()

    if args.report:
        for rel, line, kind in population:
            raw = (REPO / rel).read_text(encoding="utf-8", errors="replace")
            off = sum(len(x) + 1 for x in raw.split("\n")[:line - 1])
            print(f"{rel}:{line}\t{reason_at(raw, off + raw[off:].find('#'))}")
        print(f"\n{len(population)} #[ignore] attributes, {len(violations)} bare")
        return 0

    if len(population) < MIN_IGNORES:
        print(
            f"FAIL: found only {len(population)} #[ignore] attributes, floor is "
            f"{MIN_IGNORES}.\n"
            "      Either the scanner is broken (it reads BLANKED source — check\n"
            "      check-production-callers.py::strip_noise) or the population really\n"
            "      shrank, in which case lower MIN_IGNORES in this commit and say why."
        )
        return 1

    if violations:
        print(f"FAIL: {len(violations)} bare `#[ignore]` — every one has to say WHY:\n")
        for rel, line, kind in violations:
            what = "#[ignore]" if kind == "ignore" else "#[cfg_attr(…, ignore)]"
            print(f"  {rel}:{line}  {what}")
        print(
            "\nGive each a reason in this tree's existing style, naming the condition\n"
            "AND how to run it:\n"
            '  #[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]\n'
            '  #[ignore = "GPU: asserts a real adapter; run on hbox with --ignored"]\n'
            '  #[ignore = "needs a live, already-running Android emulator"]\n'
            "\nIf you cannot establish why a test is off, say THAT — an invented reason\n"
            "is worse than none."
        )
        return 1

    print(f"OK: {len(population)} `#[ignore]` attributes, every one carries a reason.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
