#!/usr/bin/env python3
"""check-bare-ignore.py — every `#[ignore]` has to say WHY. Attributes AND doctest fences.

Two contracts live here because they are the same disease at two altitudes: a test switched
off, and a documentation example switched off. §1 is the `#[ignore]` attribute. §2 (below,
"THE DOCTEST FENCE CONTRACT") is the ```ignore fence.


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

═══ §2 THE DOCTEST FENCE CONTRACT ═════════════════════════════════════════════════
A ```ignore fence is an example the compiler has been told not to read. On 2026-07-27
this tree had 71 of them and NOT ONE said why — and structurally none COULD, because a
fence info-string rejects unknown attributes: there is nowhere to put a reason. So the
reason goes as the FIRST CONTENT LINE INSIDE the block, where it also renders:

    /// ```ignore
    /// // IGNORED: `dregg-federation` is deliberately not a dependency of app-framework.
    /// use dregg_federation::KnownFederations;
    /// ```

The census that produced this gate found ~38 of those 71 were not structurally anything:
they were real, in-scope API examples that had DRIFTED — a missing `use`, an undefined
binding, a renamed function — and were silenced instead of fixed. A doctest is the one
form of documentation the compiler can check, so silencing it deletes the check and
leaves prose that reads exactly as authoritative as it did when it was true.

The marks and what each one MEANS (the convention this gate enforces):

    ```            compiles AND runs. The target for a drifted example.
    ```no_run      compiles + links, must not execute (binds a port, writes files,
                   spawns a shell, runs a prover). Say which, as `// NO_RUN: …`.
    ```text        not Rust at all — diagram, shell transcript, foreign source. The
                   marker IS the reason; the tree has 450+ of these already.
    ```ignore      STRUCTURAL IMPOSSIBILITY ONLY: a dependency cycle, a deliberately
                   broken exhibit, source quoted from a non-dependency. `// IGNORED: …`.

VIOLATIONS
  F1  a ```ignore fence whose first content line is not `// IGNORED: <reason>`.
      A `#`-hidden `# // IGNORED:` does NOT count — rustdoc hides it from the reader,
      and the reader is who the reason is for.
  F2  an INERT ATTRIBUTE: an info-string that mixes a doctest attribute with a token
      rustdoc does not know (`ascii,no_run`). rustdoc treats any unknown token as "not
      Rust", so the block silently stops being a doctest and the `no_run` means nothing.
      This is the `gating defaults to silence` class: a subtraction that emits no line.

BASELINE (`scripts/doctest-ignore-baseline.tsv`)
  It RATCHETS rather than walls. A row exempts one fence, keyed by (path, hash of the
  fence body) so it survives the file moving around it. ⚠ A row that no longer matches
  anything is a FAILURE, not a shrug — a repaired fence must retire its own exemption,
  or the baseline quietly becomes a list of things that used to be wrong.

Usage:
    scripts/check-bare-ignore.py               # both gates
    scripts/check-bare-ignore.py --fences      # §2 only
    scripts/check-bare-ignore.py --report      # the whole #[ignore] population
    scripts/check-bare-ignore.py --report-fences   # every doctest fence, by mark
    scripts/check-bare-ignore.py --self-test   # can it go red? (and does it stay
                                               #  quiet on the 177 prose mentions)
"""

from __future__ import annotations

import argparse
import hashlib
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

# §2's floor and its exemption ledger. The doc-comment fence population was 675 on
# 2026-07-27 (457 ```text, 71 ```ignore, 47 unmarked, 29 no_run, 15 compile_fail, …).
MIN_DOC_FENCES = 500
FENCE_BASELINE = REPO / "scripts" / "doctest-ignore-baseline.tsv"

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


# ═══ §2 THE DOCTEST FENCE READER ═══════════════════════════════════════════════════
# ⚠ `strip_noise` is the WRONG instrument here and reusing it would report zero: it
# BLANKS comments, and a doctest fence lives inside one. So this is the same lexer run
# for the opposite purpose — it keeps the doc comments and skips everything else. The
# discipline that matters is identical and is why this is not a grep: a `"```ignore"`
# inside a string literal, or inside a NON-doc `//` comment, must not be seen, and a
# ```` ```ignore ```` line inside an already-open ```` ```text ```` block is content,
# not an opener. All three occur in this tree.

# What rustdoc will accept in an info-string. Anything else makes the block NOT RUST
# (rustdoc's `LangString::parse`), which is F2's whole point.
KNOWN_FENCE_ATTRS = {
    "rust", "ignore", "should_panic", "no_run", "compile_fail",
    "test_harness", "standalone_crate", "standalone",
    "edition2015", "edition2018", "edition2021", "edition2024",
}
# The four that CHANGE what the harness does with the block. F2 only fires when one of
# these is present and therefore had something to lose.
BEHAVIOUR_FENCE_ATTRS = {"ignore", "should_panic", "no_run", "compile_fail"}

FENCE_RE = re.compile(r"^ {0,3}(?P<tok>```+|~~~+)(?P<info>.*)$")
REASON_RE = re.compile(r"^//\s*(IGNORED|NO_RUN)\s*:\s*\S")


def doc_lines(text: str) -> list[tuple[int, str]]:
    """[(1-based line, content-after-the-marker)] for every DOC comment line.

    `///` and `//!` (line) and `/** */` / `/*! */` (block, with a leading `*` column
    stripped when present). A plain `//` or `/* */` is NOT doc and is skipped, as are
    string and char literals — the three places this tree writes about fences in prose.
    """
    out: list[tuple[int, str]] = []
    i, n, line = 0, len(text), 1
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif c == "/" and text.startswith("//", i):
            start, j = line, i
            while j < n and text[j] != "\n":
                j += 1
            body = text[i:j]
            # `////…` is a rule/banner, not a doc comment (rustc agrees).
            if (body.startswith("///") and not body.startswith("////")) or body.startswith("//!"):
                out.append((start, body[3:]))
            i = j
        elif c == "/" and text.startswith("/*", i):
            is_doc = (text.startswith("/**", i) and not text.startswith("/**/", i)) \
                or text.startswith("/*!", i)
            depth, j = 0, i
            while j < n:  # Rust block comments nest.
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            if is_doc:
                inner = text[i + 3:max(i + 3, j - 2)]
                for k, raw in enumerate(inner.split("\n")):
                    lstripped = raw.lstrip()
                    out.append((line + k, lstripped[1:] if lstripped.startswith("*") else raw))
            line += text.count("\n", i, j)
            i = j
        elif c == "r" and (m := re.match(r'r(#*)"', text[i:])):
            hashes = m.group(1)
            close = text.find('"' + hashes, i + len(m.group(0)))
            end = n if close == -1 else close + 1 + len(hashes)
            line += text.count("\n", i, end)
            i = end
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            end = min(j + 1, n)
            line += text.count("\n", i, end)
            i = end
        elif c == "'" and i + 2 < n and (text[i + 1] != "\\" and text[i + 2] == "'"):
            i += 3
        else:
            i += 1
    return out


def doc_fences(text: str) -> list[dict]:
    """Every fence OPENER in a file's doc comments, with its body.

    A run of doc lines ends where the lines stop being contiguous (a new item), which
    also closes any fence left open — fences do not span items, and letting one do so
    would swallow every later fence in the file.
    """
    out: list[dict] = []
    open_tok: str | None = None
    cur: dict | None = None
    prev: int | None = None
    for ln, content in doc_lines(text):
        if prev is not None and ln > prev + 1:
            open_tok, cur = None, None
        prev = ln
        m = FENCE_RE.match(content)
        if m:
            tok, info = m.group("tok"), m.group("info").strip()
            if open_tok is None:
                open_tok = tok[0]
                cur = {"line": ln, "info": info, "body": [],
                       "attrs": {w for w in re.split(r"[,\s]+", info) if w}}
                out.append(cur)
                continue
            if tok[0] == open_tok and not info:  # a closer carries no info-string
                open_tok, cur = None, None
                continue
        if cur is not None:
            cur["body"].append(content)
    return out


def fence_reason(fence: dict) -> str | None:
    """The `// IGNORED:` / `// NO_RUN:` line, if it is the first thing a READER sees.

    `#`-hidden lines are skipped by rustdoc when it renders, so a reason behind one is
    a reason nobody reads — it does not count, and a blank line before it is fine.
    """
    for raw in fence["body"]:
        s = raw.strip()
        if not s:
            continue
        return s if REASON_RE.match(s) else None
    return None


def fence_key(rel: Path, fence: dict) -> str:
    """(path, body) identity, stable under the file moving around the fence."""
    body = "\n".join(x.strip() for x in fence["body"] if x.strip())
    return hashlib.sha1(f"{rel}\n{body}".encode()).hexdigest()[:12]


def scan_fences() -> tuple[list[dict], list[dict], int]:
    """(F1 violations, F2 violations, total fences seen)."""
    f1: list[dict] = []
    f2: list[dict] = []
    total = 0
    for path in rust_files():
        try:
            raw = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if "```" not in raw and "~~~" not in raw:
            continue
        rel = path.relative_to(REPO)
        for fence in doc_fences(raw):
            total += 1
            attrs = fence["attrs"]
            row = {"rel": rel, "line": fence["line"], "info": fence["info"],
                   "key": fence_key(rel, fence)}
            # ⚑ `no_run` IS ASKED FOR A REASON TOO, since 2026-07-28.
            #
            # This read `if "ignore" in attrs`, so a ```no_run fence was never asked. The
            # convention this gate enforces says a `no_run` block states WHAT WOULD HAPPEN if it
            # ran — writes a file, binds a port, runs a prover, costs money — and that claim is
            # exactly as unverifiable as an `ignore` without one. `REASON_RE` already accepted
            # `NO_RUN:` and the constants at :215/:221 already knew the attribute; the scan simply
            # never asked. Measured at the moment of arming: 680 fences, 43 `no_run`, 14 reasoned,
            # 29 REASONLESS — seeded into the baseline so this ratchets rather than walls.
            if (attrs & {"ignore", "no_run"}) and fence_reason(fence) is None:
                f1.append(row)
            if (attrs & BEHAVIOUR_FENCE_ATTRS) and (attrs - KNOWN_FENCE_ATTRS):
                row = dict(row, unknown=sorted(attrs - KNOWN_FENCE_ATTRS))
                f2.append(row)
    return f1, f2, total


def load_baseline() -> dict[tuple[str, str, str], str]:
    """{(kind, path, key): note}. Missing file = an empty baseline, which is stricter."""
    rows: dict[tuple[str, str, str], str] = {}
    if not FENCE_BASELINE.exists():
        return rows
    for raw in FENCE_BASELINE.read_text(encoding="utf-8").splitlines():
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        parts = raw.split("\t")
        if len(parts) < 4:
            continue
        kind, path, key, note = parts[0], parts[1], parts[2], "\t".join(parts[3:])
        rows[(kind.strip(), path.strip(), key.strip())] = note.strip()
    return rows


def apply_baseline(f1: list[dict], f2: list[dict], baseline: dict) -> tuple[list, list, list]:
    """(un-exempted F1, un-exempted F2, STALE baseline rows).

    The third element is the ratchet: a row matching nothing is a failure, because the
    alternative — shrugging at it — turns the file into a list of things that used to be
    wrong, and the next reader cannot tell which are which.
    """
    live: set[tuple[str, str, str]] = set()
    unexempt_f1, unexempt_f2 = [], []
    for kind, rows, out in (("no-reason", f1, unexempt_f1), ("inert-attr", f2, unexempt_f2)):
        for row in rows:
            k = (kind, str(row["rel"]), row["key"])
            live.add(k)
            if k not in baseline:
                out.append(row)
    return unexempt_f1, unexempt_f2, sorted(set(baseline) - live)


def fences_gate() -> int:
    f1, f2, total = scan_fences()
    baseline = load_baseline()

    if total < MIN_DOC_FENCES:
        print(
            f"FAIL: found only {total} doc-comment code fences, floor is {MIN_DOC_FENCES}.\n"
            "      A negative headline passes just as happily when the READER is broken, so\n"
            "      this asserts it saw a population. Either `doc_lines`/`doc_fences` stopped\n"
            "      seeing doc comments, or the tree really shrank — in which case lower\n"
            "      MIN_DOC_FENCES in the same commit and say why."
        )
        return 1

    unexempt_f1, unexempt_f2, stale = apply_baseline(f1, f2, baseline)
    bad = 0

    if unexempt_f1:
        bad += 1
        print(f"FAIL: {len(unexempt_f1)} ```ignore fence(s) that do not say WHY:\n")
        for row in unexempt_f1:
            print(f"  {row['rel']}:{row['line']}  ```{row['info']}")
        print(
            "\nA ```ignore is for STRUCTURAL IMPOSSIBILITY only — a dependency cycle, a\n"
            "deliberately broken exhibit, source quoted from a non-dependency. If the example\n"
            "merely drifted, REPAIR IT: give it the missing `use`, define the loose binding,\n"
            "update it to today's signature. Deleting it deletes documentation.\n"
            "\nIf it really is structural, say so on the first line INSIDE the block, where the\n"
            "reader sees it too:\n"
            '  /// ```ignore\n'
            '  /// // IGNORED: `dregg-federation` is deliberately not a dep of app-framework.\n'
        )

    if unexempt_f2:
        bad += 1
        print(f"FAIL: {len(unexempt_f2)} fence(s) whose doctest attribute is INERT:\n")
        for row in unexempt_f2:
            print(f"  {row['rel']}:{row['line']}  ```{row['info']}   "
                  f"unknown to rustdoc: {', '.join(row['unknown'])}")
        print(
            "\nrustdoc treats ANY unknown info-string token as `this block is not Rust`, so the\n"
            "attribute beside it does nothing at all — the block silently stopped being a\n"
            "doctest. Drop the unknown token, or mark the block ```text and mean it.\n"
        )

    if stale:
        bad += 1
        print(f"FAIL: {len(stale)} baseline row(s) in {FENCE_BASELINE.name} match nothing:\n")
        for kind, path, key in stale:
            print(f"  {kind}\t{path}\t{key}\t{baseline[(kind, path, key)]}")
        print(
            "\nThis is the ratchet working, not a nuisance. A fence that was repaired must\n"
            "RETIRE its own exemption — delete the row in the same commit. If the file moved,\n"
            "re-run `--report-fences` and take the new key. A baseline nobody prunes decays\n"
            "into a list of things that used to be wrong.\n"
        )

    if bad:
        return 1

    exempt = len(baseline)
    print(
        f"OK: {total} doc-comment code fences. Every ```ignore says why; no inert attributes."
        + (f" ({exempt} baselined exemption(s), all still live.)" if exempt else "")
    )
    return 0


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


# ── §2's self-test corpus ──────────────────────────────────────────────────────────
# Every MUST_NOT_CATCH_FENCE shape is one a naive `grep -F '```ignore'` gets wrong on
# THIS tree, and the last three are the ones that make the doc-comment lexer necessary
# rather than decorative.
FENCE_MUST_CATCH = [
    ("bare_ignore_fence", '/// ```ignore\n/// let x = undefined_thing();\n/// ```\nfn t() {}'),
    ("rust_ignore_fence", '//! ```rust,ignore\n//! use gone::Thing;\n//! ```\n'),
    ("inner_doc_bare", '//! ```ignore\n//! foo();\n//! ```\n'),
    # A reason nobody can read is not a reason: rustdoc hides `#`-prefixed lines.
    ("hidden_reason", '/// ```ignore\n/// # // IGNORED: a dependency cycle\n/// foo();\n/// ```\n'),
    # F2: `ascii` is unknown to rustdoc, so the block is not Rust and `no_run` is inert.
    ("inert_attribute", '/// ```ascii,no_run\n/// +---+\n/// ```\nfn t() {}'),
    # The second fence in a file must not be shadowed by the first one being fine.
    ("second_fence_after_good",
     '/// ```ignore\n/// // IGNORED: structural\n/// a();\n/// ```\nfn a() {}\n'
     '/// ```ignore\n/// b();\n/// ```\nfn b() {}'),
    # A block-doc comment is a doc comment too.
    ("block_doc", '/**\n ```ignore\n let x = 1;\n ```\n*/\nfn t() {}'),
]

FENCE_MUST_NOT_CATCH = [
    ("reasoned", '/// ```ignore\n/// // IGNORED: `dregg-federation` is not a dep here.\n'
                 '/// use dregg_federation::KnownFederations;\n/// ```\nfn t() {}'),
    ("reasoned_after_blank", '/// ```ignore\n///\n/// // IGNORED: a deliberately broken exhibit.\n'
                             '/// bad();\n/// ```\nfn t() {}'),
    ("no_run_reasoned", '/// ```no_run\n/// // NO_RUN: binds 0.0.0.0:3000.\n/// serve();\n/// ```\nfn t() {}'),
    ("plain_text_block", '/// ```text\n/// +---+---+\n/// ```\nfn t() {}'),
    # ⚠ A ```ignore INSIDE an open ```text block is content, not an opener.
    ("nested_in_text", '/// ```text\n/// mark it ```ignore when structural\n/// ```\nfn t() {}'),
    # ⚠ A doc comment that TALKS about the marker without opening a fence.
    ("prose_mention", '/// Prefer `text` over `ignore` for diagrams; ```ignore is a last resort.\nfn t() {}'),
    # ⚠ Not a doc comment at all.
    ("plain_comment", '// ```ignore\n// let x = 1;\n// ```\nfn t() {}'),
    ("banner_comment", '//// ```ignore\n//// x\n//// ```\nfn t() {}'),
    # ⚠ Inside a string literal — this tree's gate scripts embed fence text constantly.
    ("in_raw_string", 'const D: &str = r##"```ignore\nlet x = 1;\n```"##;'),
    ("in_string", 'let s = "```ignore";'),
    # A line comment holding `/*` must not open a block comment that swallows the file.
    ("glob_in_line_comment",
     '// see circuit/tests/*.rs /* not a comment opener\n'
     '/// ```ignore\n/// // IGNORED: structural.\n/// x();\n/// ```\nfn t() {}'),
    # `text`/`json`/`sh` carry no behaviour attribute, so F2 has nothing to lose.
    ("unknown_only_is_fine", '/// ```json\n/// {"a": 1}\n/// ```\nfn t() {}'),
]


def fence_self_test() -> int:
    bad = 0
    for name, src in FENCE_MUST_CATCH:
        hits = []
        for f in doc_fences(src):
            if "ignore" in f["attrs"] and fence_reason(f) is None:
                hits.append(("F1", f))
            if (f["attrs"] & BEHAVIOUR_FENCE_ATTRS) and (f["attrs"] - KNOWN_FENCE_ATTRS):
                hits.append(("F2", f))
        if not hits:
            print(f"  fence self-test MISS  (must catch) {name}")
            bad += 1
        else:
            print(f"  fence self-test caught             {name}")
    for name, src in FENCE_MUST_NOT_CATCH:
        hits = []
        for f in doc_fences(src):
            if "ignore" in f["attrs"] and fence_reason(f) is None:
                hits.append(("F1", f))
            if (f["attrs"] & BEHAVIOUR_FENCE_ATTRS) and (f["attrs"] - KNOWN_FENCE_ATTRS):
                hits.append(("F2", f))
        if hits:
            print(f"  fence self-test FALSE POSITIVE     {name}")
            bad += 1
        else:
            print(f"  fence self-test quiet on           {name}")

    # The READER has to be able to see a population, or the floor is theatre.
    seen = len(doc_fences('/// ```text\n/// a\n/// ```\n/// ```ignore\n/// b\n/// ```\nfn t() {}'))
    if seen != 2:
        print(f"  fence self-test: reader counted {seen} fences on a two-fence input, want 2")
        bad += 1

    # The baseline key must be stable under the file moving around the fence, and
    # DIFFERENT when the fence body changes — otherwise an exemption silently covers
    # a rewritten example.
    a = doc_fences('/// ```ignore\n/// x();\n/// ```\nfn t() {}')[0]
    b = doc_fences('fn pad() {}\n\n/// ```ignore\n/// x();\n/// ```\nfn t() {}')[0]
    c = doc_fences('/// ```ignore\n/// y();\n/// ```\nfn t() {}')[0]
    p = Path("a/b.rs")
    if fence_key(p, a) != fence_key(p, b):
        print("  fence self-test: baseline key moved when only the LINE moved")
        bad += 1
    if fence_key(p, a) == fence_key(p, c):
        print("  fence self-test: baseline key did NOT move when the BODY changed")
        bad += 1

    # ⚠ THE RATCHET, driven through the real decision path. Three properties, and the
    # third is the one that keeps the file honest.
    rows = [{"rel": Path("a/b.rs"), "line": 3, "info": "ignore", "key": "aaaaaaaaaaaa"},
            {"rel": Path("a/c.rs"), "line": 9, "info": "ignore", "key": "bbbbbbbbbbbb"}]
    base = {("no-reason", "a/b.rs", "aaaaaaaaaaaa"): "known remainder",
            ("no-reason", "a/gone.rs", "cccccccccccc"): "repaired — should be pruned"}
    un1, un2, stale = apply_baseline(rows, [], base)
    if [r["key"] for r in un1] != ["bbbbbbbbbbbb"]:
        print("  fence self-test: baseline exempted the wrong fence (or none)")
        bad += 1
    if not stale or stale[0][1] != "a/gone.rs":
        print("  fence self-test: a STALE baseline row did not fail the gate")
        bad += 1
    if apply_baseline(rows, [], {})[0] != rows:
        print("  fence self-test: an EMPTY baseline did not leave every finding live")
        bad += 1

    print()
    if bad:
        print(f"FENCE SELF-TEST FAILED: {bad} case(s)")
        return 1
    print(f"FENCE SELF-TEST PASSED: {len(FENCE_MUST_CATCH)} caught, "
          f"{len(FENCE_MUST_NOT_CATCH)} correctly quiet")
    return 0


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


def report_fences() -> int:
    by_mark: dict[str, int] = {}
    rows = []
    for path in rust_files():
        try:
            raw = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if "```" not in raw and "~~~" not in raw:
            continue
        rel = path.relative_to(REPO)
        for fence in doc_fences(raw):
            mark = fence["info"] or "(runs)"
            by_mark[mark] = by_mark.get(mark, 0) + 1
            if "ignore" in fence["attrs"]:
                rows.append((rel, fence["line"], fence["info"],
                             fence_key(rel, fence), fence_reason(fence) or "— NO REASON —"))
    for rel, line, info, key, reason in rows:
        print(f"{rel}:{line}\t{key}\t```{info}\t{reason[:110]}")
    print()
    for mark, n in sorted(by_mark.items(), key=lambda x: -x[1]):
        print(f"{n:5d}  ```{mark}")
    print(f"\n{sum(by_mark.values())} doc-comment fences, {len(rows)} of them ```ignore")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--report", action="store_true", help="print the whole population")
    ap.add_argument("--report-fences", action="store_true",
                    help="every doctest fence, by mark, with baseline keys")
    ap.add_argument("--fences", action="store_true", help="run only the doctest-fence contract")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.report_fences:
        return report_fences()

    if args.self_test:
        if args.fences:
            return fence_self_test()
        rc = self_test()
        print()
        return max(rc, fence_self_test())

    if args.fences:
        return fences_gate()

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
    # §2 rides the same invocation so it cannot be the leg someone forgets to wire.
    return fences_gate()


if __name__ == "__main__":
    sys.exit(main())
