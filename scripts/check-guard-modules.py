#!/usr/bin/env python3
"""check-guard-modules.py — a metatheory/Dregg2 module that CARRIES a differential
guard (`#guard` / `#assert_axioms` / `#assert_namespace_axioms`) but is UNROOTED (in
no default `lake build` target) or SORRY-CARRYING. Either way its guard never runs
as a real check, so its headline is a claim nobody verified.

═══ THE EXACT WOUND (2026-08-01) ══════════════════════════════════════════════════
`Dregg2.Bridge.MinaWrapFtEval0Weld` carried a `#guard`-backed headline — "six gate
bodies reproduce the linearization constant term" — AND a `GAMMA_CHAL` `sorry` FROM
ITS BIRTH COMMIT (`bb7c0d7e3`). It was in NO default lake target, so `lake build`
never compiled it, so its `#guard` NEVER RAN, so the headline was never
machine-checked. When a lane finally forced it to compile it found the guard ALSO sat
downstream of a real `gateLinConst` defect. Two silences stacked: gating-defaults-to-
silence (unrooted ⇒ the guard cannot fire) and a `sorry` (the guard, even if it fired,
is vacuous below the hole).

A `#guard`/`#assert_axioms` is a NEGATIVE assertion: it is supposed to be able to go
red. An unrooted one, or one below a `sorry`, is a negative assertion that CANNOT go
red — the exact disease this repo keeps getting bitten by, pointed at its own
instruments. This gate makes that mechanical: a module that CLAIMS something checkable
must actually be checked.

═══ WHAT IS A GUARD-CARRYING MODULE ═══════════════════════════════════════════════
A `metatheory/Dregg2/**.lean` whose source (comments and string literals stripped —
this tree names `#assert_axioms` constantly in prose, `…#assert_axioms-clean`, so a
raw grep is dominated by false hits) contains one of:
    #guard            — a value/decide differential
    #assert_axioms    — a keystone pinned to the kernel-clean axiom triple
    #assert_namespace_axioms  — the same, namespace-wide
These are the differential/vacuity gates. A module that carries one is asserting a
checkable fact; if it is not built, the fact is unasserted.

═══ THE TWO ARMS, AND WHY EACH IS A DEFECT ════════════════════════════════════════
  (a) UNROOTED. The module is reachable from NO library in `lakefile.toml`'s
      `defaultTargets` (transitively, over `import` edges). `lake build` never
      compiles it, so its guards run in no plain build and in no CI that runs a plain
      build. Seeds are computed from the lakefile the same way `check-lean-orphans.sh`
      does: globbed libs (`Metatheory.+`, `Polis.+`, `Dregg2.PicklesSynthesis`) seed
      every matching module; root-module libs (`Dregg2`, `Market`, `Bfv`) seed their
      root and the BFS pulls the import closure.

      ⚠ This is STRICTER than `check-lean-orphans.sh`, on purpose. That gate lets an
      orphan through if it is in `lean-orphans-allow.txt` ("the exclusion is
      deliberate"). Here, a guard-carrying orphan is NOT waved through by that list: a
      module can be a deliberate WIP orphan and still be lying about being checked. The
      whole point of a guard is that it fires; a guard that is deliberately never built
      is a deliberate silent claim.

  (b) SORRY. A ROOTED guard-carrying module that carries a real `sorry` / `sorryAx`
      term / `admit` tactic. Its guards DO run, but a `#guard`/`#assert_axioms`
      downstream of a `sorry` is vacuous — it green-passes on a proof with a hole. (The
      sorry arm is scoped to ROOTED modules because an UNROOTED module is already
      reported by arm (a); once it is rooted, the sorry surfaces here — which is
      precisely the MinaWrapFtEval0Weld sequence.)

═══ HOLE DETECTION IS PRECISE, NOT A GREP ═════════════════════════════════════════
`grep sorry` over Lean is dominated by prose and IDENTIFIERS in this tree:
  * `admit` is a heavily-used identifier here — a structure field (`admit : Int → Int →
    Bool`, an "admission predicate") and a top-level `def admit` (`Dregg2.Upgrade`).
    A bare `\badmit\b` reports ~6 false positives and zero real tactics.
  * `sorryAx` appears as a NAME LITERAL inside axiom-classifier guards —
    `#guard (classifyAxioms false #[``sorryAx]).label == "ExtraAxioms"` deliberately
    references the name to prove the classifier flags it. That is not a hole.
So detection runs on comment/string-stripped source and:
  * `sorry`   — bare, not `sorryAx`, not identifier-embedded, not name-quoted.
  * `sorryAx` — as a TERM, not `` `sorryAx `` / `` ``sorryAx `` (name-quoted).
  * `admit`   — only as a bare argument-less TACTIC in tactic position, never the
    `admit :`/`admit :=`/`x.admit`/`admit y` identifier forms.
Measured at the commit that added this gate, this reports exactly ONE real hole across
all ~1990 Dregg2 modules (`Dregg2.Bignum.LedgerBalance:456`, the named completeness
pole) and zero false positives.

═══ WHAT THIS DOES NOT CATCH — read before trusting a green ════════════════════════
  * A TAUTOLOGICAL guard. `#guard 1 == 1`, `#assert_axioms trivial_lemma`, a `#guard`
    over a `by rfl` fact that says nothing — these are ROOTED and SORRY-FREE and pass
    here. This gate closes SYNTACTIC vacuity (never built / built below a hole); it does
    NOT close SEMANTIC vacuity (built, fires, asserts nothing). That is a harder,
    separate residual — it needs reading what the guard claims, not whether it runs —
    and this gate does not pretend to solve it.
  * ELABORATION-INDUCED `sorryAx` with no source token. A Type mismatch can inject
    `sorryAx` at elaboration with no `sorry` in the text (the ~28 `Circuit.Emit/*Refine`
    modules the orphan gate documents). A pure text scan cannot see that. But such a
    module is RED at build, and if it is ROOTED that redness is a build failure caught
    elsewhere (axiom-hygiene-guard); if UNROOTED it is caught here by arm (a).
  * Whether a ROOTED module's guard actually EXECUTED in a given CI run. Rootedness is
    a necessary condition (it CAN run), not a witness that a particular run ran it.

═══ THE RATCHET ═══════════════════════════════════════════════════════════════════
Like `check-lean-orphans.sh`, a large pre-existing population (measured: 77 unrooted +
1 sorry at HEAD 2026-08-01) is recorded in `scripts/guard-modules-baseline.txt` — a
BURNDOWN LEDGER, not an acceptance list. A guard-carrying orphan is a wound to ROOT,
not a permanent exemption. The gate:
  * FAILS on any (arm, module) NOT in the baseline — the NEXT MinaWrapFtEval0Weld reds
    immediately and stands out against a green steady state.
  * FAILS on a STALE baseline row (module now rooted / sorry gone / file deleted) — so
    fixing a module forces retiring its row, and the census can only ratchet DOWN.
  * FAILS on a row whose WEIGHT DRIFTED — see below; the weight is what makes the
    ledger's TOTAL a number that means something.
  * PRINTS the full census every run — the backlog is visible and named, never buried.
`--census` ignores the baseline and exits non-zero on the RAW census (every violation),
which is the "report every silent claim" view.

═══ ⚑ EVERY ROW CARRIES A WEIGHT, AND THE WEIGHT IS THE POINT ═════════════════════
A row is `<kind> <module> <n>`, where **n is the number of guard commands that this
wound silences** — every `#guard`/`#assert_axioms`/`#assert_namespace_axioms` in an
UNROOTED module runs in no build, and every one in a SORRY module sits below a hole.
So the ledger's TOTAL is a single honest quantity: *how many differential guards in
this tree are not actually checking anything*.

Rows alone cannot see the laundering shape. One unrooted module carrying 838 guards,
split into thirteen unrooted modules carrying 861, adds twelve rows and raises the real
population by 23 — and **no row rises**, because the original's row vanishes and the
pieces are new rows that arm (c) would even DEMAND exist. That is exactly the operation
`check-guard-discipline.py` measured on 2026-08-02 (`935d8ef09`, +23 guards, `rows_up=0`),
and only a TOTAL can see it. Hence the weight, and hence (d2) below.

⚠ The weight is graded in BOTH directions at gate time, and that is load-bearing rather
than fussy. If a row were allowed to sit ABOVE its live weight, the ledger would hold
slack — and a refresh could then spend that slack on new wounds while the recorded total
never rose. `(d2)` is only sound because the ledger is exact.

═══ ⚑⚑ THE REFRESH GATE — arms (d1)/(d2)/(d3), and why they exist ═════════════════
Every arm above grades the CENSUS against the BASELINE. Until 2026-08-02 this tool had
**no `--update-baseline` at all**: the documented way to move the ledger was to HAND-ADD
rows, and nothing bounded the row count or the weight. An editor could add rows freely
and the gate never objected — the escape hatch was the whole back wall.

The neighbouring `check-guard-discipline.py` had the same hole in tool form, and it was
not hypothetical there: a module SPLIT walked 23 guards into the ledger while no row
rose, and the next honest burndown (−14) made the two-commit window read as noise. So
the refresh here is gated from birth, on:

  (d0) **the census must not be VACUOUS**. A refresh from a blinded scan would WIPE the
       ledger and the ratchet would happily accept it — every row "fell". The floors run
       before anything is written.
  (d1) **no surviving row's WEIGHT may RISE** — a tracked orphan may not quietly
       accumulate more silent guards.
  (d2) **the TOTAL WEIGHT may not RISE** — the split/rename arm. A genuine split's
       pieces sum to at most the original, so a level split still passes; only growth is
       refused. (The ROW COUNT is reported but deliberately NOT ratcheted: a pure
       refactor that splits one orphan in two changes no guard's fate, and the weight
       already sees every real growth, so ratcheting rows would red on a non-defect.)
  (d3) **every refresh RECORDS PROVENANCE** — sha, whether the tree was DIRTY, both
       totals, the delta, a verdict, and a mandatory `--reason`, stamped into the header.
       Dirtiness is recorded rather than refused because "which tree did this number come
       from" is precisely the question a laundered refresh makes unanswerable.

`--only <selector>` (repeatable) is the DEFAULT way to retire rows. The tree is shared:
a whole-census refresh absorbs every other lane's in-flight guard-carrying orphan — the
laundering shape again, with a sibling's work as the payload. `--only` refreshes exactly
the rows you name and leaves every other row standing, and is still subject to (d1)/(d2).
A selector is `Dregg2.Foo.Bar` (both arms of that module) or `unrooted:Dregg2.Foo.Bar`.

⚠ THE OVERRIDE IS LOUD, NOT ABSENT. `--allow-increase` exists, still requires `--reason`,
and stamps `INCREASED` with the delta. A ban with no escape hatch gets routed around by
hand-editing the file, which is the silent outcome this gate exists to prevent.

═══ ⚑ ARM (e): THE LEDGER CHECKS ITSELF, ON EVERY ORDINARY RUN ════════════════════
(d0)–(d3) gate a TOOL, and a tool is only a gate for the people who run it. Nothing stops
an editor from typing a row upward or pasting a new one in. So the baseline is
self-checking, and the check runs on the ORDINARY invocation rather than only on refresh:

  * the header carries `# TOTAL <w> guards across <r> rows`, and
  * the last `# BASELINE-PROVENANCE` line carries the totals that refresh produced,
  * and both must equal the rows actually present.

A hand-edit that raises a weight, or adds a row, and does not also forge two more numbers
REDS for anyone who runs the gate, with no access to history required. A baseline with no
header, or carrying a row the gate cannot read, is refused as "not written by the gated
refresh" — which is the shape a file assembled by some other means would have.

═══ USAGE ═════════════════════════════════════════════════════════════════════════
  python3 scripts/check-guard-modules.py                 # working tree, ratcheted
  python3 scripts/check-guard-modules.py --rev HEAD      # clean extract of HEAD (churn-safe)
  python3 scripts/check-guard-modules.py --census        # raw census, ignore baseline
  python3 scripts/check-guard-modules.py --print-census  # list every violation, exit 0
  python3 scripts/check-guard-modules.py --update-baseline --only Dregg2.Foo --reason "rooted it"
  python3 scripts/check-guard-modules.py --update-baseline --allow-increase --reason "..."
  python3 scripts/check-guard-modules.py --self-test     # red-proof (synthetic tree)
Exit: 0 clean/ratchet-green · 1 violation, stale row, weight drift, vacuous scan, or a
      baseline that does not add up · 2 environment error · 3 REFUSED refresh (not written)
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

# ── the three guard commands (exact tokens; a following identifier char excludes
# `#guard_msgs`, `#assert_axioms` is not a prefix of another command) ─────────────
GUARD_RE = re.compile(r'#(?:guard|assert_axioms|assert_namespace_axioms)(?![A-Za-z0-9_])')

# ── precise hole tokens (run on comment/string-stripped source) ───────────────────
# bare `sorry` — not `sorryAx`, not identifier-embedded (`sorry_free`), not member/name (`.sorry`, `` `sorry ``)
SORRY_RE = re.compile(r'(?<![A-Za-z0-9_.`])sorry(?![A-Za-z0-9_])')
# `sorryAx` as a TERM — excludes the name-quoted `` `sorryAx `` / `` ``sorryAx `` (backtick precedes)
SORRYAX_RE = re.compile(r'(?<![A-Za-z0-9_.`])sorryAx(?![A-Za-z0-9_])')
# `admit` TACTIC only: bare (no trailing args, no `:`/`:=`), in tactic position, not `x.admit`
ADMIT_RE = re.compile(r'(?:(?<=\bby)|(?<=;)|(?<=>)|(?<=·)|(?<=\|)|^)\s*admit\s*(?=$|;|<|\)|\})')

# ── non-vacuity floors (a scan that finds far fewer than the corpus carries has a
# broken stripper/regex/extract and must FAIL rather than green having checked nothing) ──
MIN_DREGG2_FILES = 1500     # the corpus is ~1990
MIN_GUARD_MODULES = 1000    # guard-carrying population is ~1667
MIN_REACHABLE = 500         # reachable closure is ~2000

IGNORE_DIRS = {".lake", ".git", "build", "__pycache__"}

KINDS = ("unrooted", "sorry")


def repo_root() -> Path:
    here = Path(__file__).resolve().parent
    try:
        out = subprocess.run(
            ["git", "-C", str(here), "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        )
        return Path(out.stdout.strip())
    except Exception:
        return here.parent


DEFAULT_BASELINE = repo_root() / "scripts" / "guard-modules-baseline.txt"


def strip_lean_noise(text: str) -> str:
    """Blank Lean comments and string literals, PRESERVING newline offsets (so a hit's
    line number still indexes the original). Handles `--` line comments, NESTED `/- -/`
    block comments (doc `/-- -/` included, they open with `/-`), and `"…"` strings with
    `\\` escapes. A real lexer, not a regex pair: a `/-` inside a `--` line is not a
    block open, and a guard token inside a string is not a guard."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "-" and i + 1 < n and text[i + 1] == "-":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif c == "/" and i + 1 < n and text[i + 1] == "-":
            depth = 0
            while i < n:
                if text.startswith("/-", i):
                    depth += 1
                    out[i] = out[i + 1] = " "
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    out[i] = out[i + 1] = " "
                    i += 2
                    if depth == 0:
                        break
                else:
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
        elif c == '"':
            out[i] = " "
            j = i + 1
            while j < n and text[j] != '"':
                if text[j] == "\\" and j + 1 < n:
                    if text[j] != "\n":
                        out[j] = " "
                    if text[j + 1] != "\n":
                        out[j + 1] = " "
                    j += 2
                else:
                    if text[j] != "\n":
                        out[j] = " "
                    j += 1
            if j < n:
                out[j] = " "
            i = j + 1
        else:
            i += 1
    return "".join(out)


# ─────────────────────────────────────────────────────────────────────────────────
# module <-> path, corpus walk, imports
# ─────────────────────────────────────────────────────────────────────────────────
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")


def mod_to_path(mt: Path, m: str) -> Path:
    return mt / (m.replace(".", "/") + ".lean")


def path_to_mod(mt: Path, p: Path) -> str:
    return str(p.relative_to(mt))[:-5].replace("/", ".")


def all_modules(mt: Path) -> set[str]:
    out: set[str] = set()
    for dp, dns, fns in os.walk(mt):
        dns[:] = [d for d in dns if d not in IGNORE_DIRS]
        for fn in fns:
            if fn.endswith(".lean"):
                out.add(path_to_mod(mt, Path(dp) / fn))
    return out


def imports_of(mt: Path, m: str) -> list[str]:
    p = mod_to_path(mt, m)
    out: list[str] = []
    try:
        with open(p, encoding="utf-8", errors="replace") as f:
            for line in f:
                mm = IMPORT_RE.match(line)
                if mm:
                    out.append(mm.group(1))
    except OSError:
        pass
    return out


# ─────────────────────────────────────────────────────────────────────────────────
# reachability from the lakefile's defaultTargets (the set `lake build` compiles)
# ─────────────────────────────────────────────────────────────────────────────────
def lakefile_seeds(mt: Path, allmods: set[str]) -> tuple[set[str], list[str]]:
    """Parse lakefile.toml -> seed modules of every default target. Returns
    (seeds, default_targets). Mirrors Lake's own lib semantics:
      globbed lib  "Foo.+" -> Foo and all descendants; "Foo.*" -> descendants;
                   plain "Foo" -> just Foo (only modules that exist in-tree seed).
      root lib     no globs -> the lib's `roots` (default [name]); BFS pulls the closure.
    """
    lf = mt / "lakefile.toml"
    with open(lf, "rb") as f:
        doc = tomllib.load(f)
    targets = list(doc.get("defaultTargets", []))
    libs = {l["name"]: l for l in doc.get("lean_lib", [])}
    seeds: set[str] = set()
    for t in targets:
        lib = libs.get(t)
        if lib is None:
            # a defaultTarget with no lean_lib (e.g. an exe); its own root is a seed.
            seeds.add(t)
            continue
        globs = lib.get("globs")
        if globs:
            for g in globs:
                if g.endswith(".+"):
                    pre = g[:-2]
                    seeds |= {m for m in allmods if m == pre or m.startswith(pre + ".")}
                elif g.endswith(".*"):
                    pre = g[:-2]
                    seeds |= {m for m in allmods if m.startswith(pre + ".")}
                else:
                    if g in allmods:
                        seeds.add(g)
        else:
            roots = lib.get("roots", [t])
            if isinstance(roots, str):
                roots = [roots]
            seeds |= set(roots)
    return seeds, targets


def reachable_set(mt: Path, seeds: set[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(seeds)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        if not mod_to_path(mt, m).is_file():  # external (Mathlib.*/Std.*) — terminates
            continue
        seen.add(m)
        for im in imports_of(mt, m):
            if im not in seen:
                stack.append(im)
    return seen


# ─────────────────────────────────────────────────────────────────────────────────
# guard-carrying modules + hole findings
# ─────────────────────────────────────────────────────────────────────────────────
def module_text(mt: Path, m: str) -> str:
    try:
        return mod_to_path(mt, m).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def guard_count(stripped: str) -> int:
    """How many differential guards this module asserts. This is a row's WEIGHT: if the
    module is unrooted every one of them runs in no build; if it carries a hole every one
    of them may be vacuous."""
    return len(GUARD_RE.findall(stripped))


def carries_guard(stripped: str) -> bool:
    return GUARD_RE.search(stripped) is not None


def hole_hits(stripped: str) -> list[tuple[int, str]]:
    """(line, token) for every real sorry/sorryAx/admit-tactic in stripped source."""
    hits: list[tuple[int, str]] = []
    for ln, line in enumerate(stripped.split("\n"), 1):
        if SORRY_RE.search(line):
            hits.append((ln, "sorry"))
        if SORRYAX_RE.search(line):
            hits.append((ln, "sorryAx"))
        if ADMIT_RE.search(line):
            hits.append((ln, "admit"))
    return hits


class Census:
    def __init__(self) -> None:
        self.dregg2_files = 0
        self.guard_modules = 0
        self.reachable = 0
        self.unrooted: list[tuple[str, int]] = []              # (module, guards carried)
        self.sorry: list[tuple[str, int, int, str]] = []       # (module, guards, line, token)

    def rows(self) -> dict[tuple[str, str], tuple[int, str]]:
        """(kind, module) -> (weight, detail). One row per wound; weight = the guards it
        silences. A module with several holes is ONE `sorry` row (the detail names them)."""
        out: dict[tuple[str, str], tuple[int, str]] = {}
        for m, w in self.unrooted:
            out[("unrooted", m)] = (w, f"{w} guard(s) reachable from no default lake target")
        holes: dict[str, tuple[int, list[str]]] = {}
        for m, w, ln, tok in self.sorry:
            holes.setdefault(m, (w, []))[1].append(f"`{tok}`@{ln}")
        for m, (w, toks) in holes.items():
            shown = ", ".join(toks[:4]) + (f" +{len(toks) - 4} more" if len(toks) > 4 else "")
            out[("sorry", m)] = (w, f"{w} guard(s) below {shown}")
        return out

    def total_weight(self) -> int:
        return sum(w for w, _ in self.rows().values())

    def violations(self) -> list[tuple[str, str, int, str]]:
        """(kind, module, weight, detail), sorted — the printable census."""
        return [(k, m, w, d) for (k, m), (w, d) in sorted(self.rows().items())]


def scan(mt: Path, scope_prefix: str = "Dregg2") -> Census:
    c = Census()
    allmods = all_modules(mt)
    seeds, _ = lakefile_seeds(mt, allmods)
    reach = reachable_set(mt, seeds)
    c.reachable = len(reach)

    scoped = sorted(m for m in allmods if m.startswith(scope_prefix + "."))
    c.dregg2_files = len(scoped)

    for m in scoped:
        stripped = strip_lean_noise(module_text(mt, m))
        g = guard_count(stripped)
        if not g:
            continue
        c.guard_modules += 1
        if m not in reach:
            c.unrooted.append((m, g))
            continue  # sorry arm is scoped to ROOTED modules (unrooted already reported)
        for ln, tok in hole_hits(stripped):
            c.sorry.append((m, g, ln, tok))
    c.unrooted.sort()
    c.sorry.sort()
    return c


# ─────────────────────────────────────────────────────────────────────────────────
# baseline (burndown ledger) — rows, header integrity, provenance
# ─────────────────────────────────────────────────────────────────────────────────
Rows = dict[tuple[str, str], tuple[int, str]]   # (kind, module) -> (weight, reason)

PROV_PREFIX = "# BASELINE-PROVENANCE"
TOTAL_RE = re.compile(r'^#\s*TOTAL\s+(\d+)\s+guards?\s+across\s+(\d+)\s+rows', re.MULTILINE)
PROV_TAIL_RE = re.compile(r'W:(\d+)\s*(?:→|->)\s*(\d+).*?R:(\d+)\s*(?:→|->)\s*(\d+)')


def parse_baseline(path: Path) -> tuple[Rows, list[str]]:
    """Rows `KIND MODULE WEIGHT [# reason]` -> ((kind, module) -> (weight, reason)), plus
    every line the gate could NOT read. An unreadable row is not skipped quietly: a row
    with no weight column is the OLD hand-maintained format, and arm (e) refuses it —
    silently ignoring it is how a ledger stops meaning what its header says."""
    rows: Rows = {}
    malformed: list[str] = []
    if not path.is_file():
        return rows, malformed
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        body, _, reason = s.partition("#")
        parts = body.split()
        if len(parts) < 3 or parts[0] not in KINDS or not parts[2].isdigit():
            malformed.append(s)
            continue
        rows[(parts[0], parts[1])] = (int(parts[2]), reason.strip())
    return rows, malformed


def read_baseline(path: Path) -> Rows:
    return parse_baseline(path)[0]


def read_provenance(path: Path) -> list[str]:
    """The refresh log carried in the baseline header, oldest first."""
    if not path.is_file():
        return []
    return [ln.rstrip() for ln in path.read_text(encoding="utf-8", errors="replace").splitlines()
            if ln.startswith(PROV_PREFIX)]


def audit_baseline_integrity(path: Path) -> list[str]:
    """⚑ ARM (e) — THE LEDGER CHECKS ITSELF, so the refresh gate cannot be walked around
    with an editor. (d0)–(d3) live in `refresh_baseline`, which is a TOOL, and a tool is
    only a gate for the people who run it. What DOES stop a hand-edit being silent: the
    header's `# TOTAL <w> guards across <r> rows` and the last provenance line's totals
    must both equal the rows actually present. Runs on every ordinary invocation."""
    if not path.is_file():
        return []
    rows, malformed = parse_baseline(path)
    weight, nrows = sum(w for w, _ in rows.values()), len(rows)
    text = path.read_text(encoding="utf-8", errors="replace")
    findings: list[str] = []

    if malformed:
        findings.append(
            f"{len(malformed)} baseline line(s) the gate CANNOT READ (a row is "
            "`<unrooted|sorry> <module> <weight>`): "
            + "; ".join(repr(x) for x in malformed[:3])
            + (f" … +{len(malformed) - 3} more" if len(malformed) > 3 else "")
            + " — this file was not written by the gated refresh")

    hits = TOTAL_RE.findall(text)
    if not hits:
        findings.append("the baseline header has no `# TOTAL <w> guards across <r> rows` line "
                        "— it was not written by the gated refresh")
    elif len(hits) > 1:
        findings.append(f"the baseline header carries {len(hits)} `# TOTAL` lines — exactly one "
                        "is written by a refresh; the extras were added by hand")
    else:
        hw, hr = int(hits[0][0]), int(hits[0][1])
        if hw != weight:
            findings.append(
                f"the header says TOTAL {hw} guards but the rows carry {weight} "
                f"({weight - hw:+d}) — the ledger was EDITED without going through "
                "`--update-baseline`, which is the one path that records why")
        if hr != nrows:
            findings.append(
                f"the header says {hr} rows but {nrows} are present ({nrows - hr:+d}) — a row "
                "was added or deleted by hand")

    prov = read_provenance(path)
    if prov:
        pm = PROV_TAIL_RE.search(prov[-1])
        if pm:
            if int(pm.group(2)) != weight:
                findings.append(
                    f"the last BASELINE-PROVENANCE line ends at W:{pm.group(2)} but the rows "
                    f"carry {weight} — a weight moved after the last recorded refresh")
            if int(pm.group(4)) != nrows:
                findings.append(
                    f"the last BASELINE-PROVENANCE line ends at R:{pm.group(4)} but {nrows} rows "
                    "are present — a row moved after the last recorded refresh")
    return findings


BASELINE_PREAMBLE = [
    "# guard-modules-baseline.txt — the BURNDOWN LEDGER for scripts/check-guard-modules.py.",
    "#",
    "# Each row is a metatheory/Dregg2 module that CARRIES a differential guard",
    "# (#guard / #assert_axioms / #assert_namespace_axioms) but is either UNROOTED (built by",
    "# no default lake target, so its guard never runs) or carries a real SORRY (its guard",
    "# runs but is vacuous below the hole). This is the MinaWrapFtEval0Weld class: a headline",
    "# nobody machine-checked.",
    "#",
    "# THIS IS A BURNDOWN LEDGER, NOT AN ACCEPTANCE LIST. A guard-carrying orphan is a wound",
    "# to ROOT (add `import <module>` to metatheory/Dregg2.lean), not a permanent exemption.",
    "# The gate FAILS on any (kind, module) NOT listed here (the NEXT silent claim reds",
    "# immediately), on a STALE row (the module got rooted / the sorry got discharged / the",
    "# file was deleted), and on a row whose WEIGHT DRIFTED in either direction — so a fix",
    "# must retire its own row and the census can only ratchet DOWN. Run",
    "# `python3 scripts/check-guard-modules.py --census` for the raw view that ignores this",
    "# ledger entirely.",
    "#",
    "# ⚑ THE WEIGHT is how many guard commands the wound SILENCES. The TOTAL below is",
    "# therefore one honest number: how many differential guards in this tree are not",
    "# actually checking anything.",
    "#",
    "# ⚑⚑ DO NOT HAND-EDIT THIS FILE. It is written by",
    "#      check-guard-modules.py --update-baseline --only <module> --reason '<why>'",
    "#    which REFUSES to raise any row's weight (d1) or the TOTAL (d2) — the total is what",
    "#    catches a module SPLIT, which grows the population while no row grows — and which",
    "#    REQUIRES a reason (d3), stamped below with the sha and whether the tree was dirty.",
    "#    Raising anything at all needs `--allow-increase --reason` and is stamped INCREASED.",
    "#    A hand-edit is DETECTED on the next ordinary gate run: the header totals and the",
    "#    last provenance line must both equal the rows actually present (arm (e)).",
    "#",
]


def orphan_allow_modules(root: Path | None = None) -> set[str]:
    """`lean-orphans-allow.txt` — the list `check-lean-orphans.sh` waves through. A
    guard-carrying orphan is NOT waved through here, but whether it is at least a TRACKED
    orphan is the single most useful thing a new row's reason can say."""
    p = (root or repo_root()) / "scripts" / "lean-orphans-allow.txt"
    out: set[str] = set()
    if not p.is_file():
        return out
    for raw in p.read_text(encoding="utf-8", errors="replace").splitlines():
        s = raw.split("#", 1)[0].strip()
        if s:
            out.add(s)
    return out


def default_reason(kind: str, module: str, detail: str, allow: set[str]) -> str:
    if kind == "unrooted":
        return ("also-orphan-allow" if module in allow
                else "UNTRACKED-ORPHAN — root first")
    return detail


def write_baseline(path: Path, rows: Rows, provenance: list[str]) -> None:
    weight = sum(w for w, _ in rows.values())
    n_unrooted = sum(1 for k, _ in rows if k == "unrooted")
    n_sorry = sum(1 for k, _ in rows if k == "sorry")
    lines = list(BASELINE_PREAMBLE)
    lines.append(f"# TOTAL {weight} guards across {len(rows)} rows "
                 f"({n_unrooted} unrooted, {n_sorry} sorry).")
    lines.append("# FORMAT  <unrooted|sorry><TAB><dotted module><TAB><guards it silences>"
                 "<TAB># reason / owner")
    lines.extend(provenance)
    for kind, banner in (("unrooted", "── UNROOTED (its guards run in no default lake target) ──"),
                         ("sorry", "── SORRY (rooted; a guard below a real hole is vacuous) ──")):
        sel = sorted(k for k in rows if k[0] == kind)
        if not sel:
            continue
        lines.append("")
        lines.append(f"# {banner}")
        for k in sel:
            w, reason = rows[k]
            lines.append(f"{k[0]}\t{k[1]}\t{w}\t# {reason}" if reason
                         else f"{k[0]}\t{k[1]}\t{w}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _head_sha_and_dirt() -> tuple[str, bool]:
    """(sha, tree-is-dirty). ⚑ Dirtiness is RECORDED, not refused: 'which tree did this
    number come from' is exactly the question a laundered refresh makes unanswerable."""
    root = repo_root()
    try:
        sha = subprocess.run(["git", "-C", str(root), "rev-parse", "--short", "HEAD"],
                             capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        return ("unknown", True)
    try:
        st = subprocess.run(["git", "-C", str(root), "status", "--porcelain", "--", "metatheory"],
                            capture_output=True, text=True, check=True).stdout.strip()
        return (sha, bool(st))
    except Exception:
        return (sha, True)


def parse_selectors(only: list[str]) -> set[tuple[str, str]]:
    """`Dregg2.Foo` -> both arms of that module; `unrooted:Dregg2.Foo` -> that arm only."""
    sel: set[tuple[str, str]] = set()
    for s in only:
        s = s.strip()
        if ":" in s:
            kind, _, module = s.partition(":")
            if kind not in KINDS:
                raise ValueError(f"--only selector {s!r}: kind must be one of {KINDS}")
            sel.add((kind, module))
        else:
            for kind in KINDS:
                sel.add((kind, s))
    return sel


def refresh_baseline(path: Path, c: Census, reason: str | None, allow_increase: bool,
                     quiet: bool = False, only: list[str] | None = None,
                     enforce_floors: bool = True) -> int:
    """⚑ THE REFRESH GATE. 0 on a written baseline, 3 on a REFUSED one.

    Kept separate from `evaluate` on purpose: `evaluate` grades a CENSUS against a LEDGER,
    this grades a proposed LEDGER against the standing one. Conflating them is exactly how
    a refresh path ends up ungated — and this tool's refresh path did not merely end up
    ungated, it did not EXIST, so the documented way to move the ledger was to hand-add
    rows and nothing bounded the count."""
    def say(*a):
        if not quiet:
            print(*a)

    old = read_baseline(path)
    allow = orphan_allow_modules()
    live = c.rows()
    proposed: Rows = {
        k: (w, old[k][1] if k in old and old[k][1] else default_reason(k[0], k[1], d, allow))
        for k, (w, d) in live.items()
    }

    unmatched: list[str] = []
    if only is not None:
        sel = parse_selectors(only)
        known = set(old) | set(proposed)
        for s in only:
            if not any(k in known for k in parse_selectors([s])):
                unmatched.append(s)
        merged: Rows = dict(old)
        for k in known:
            if k not in sel:
                continue
            if k in proposed:
                merged[k] = proposed[k]
            else:
                merged.pop(k, None)
        untouched = sorted(k for k in proposed if k not in old and k not in sel)
        proposed = merged
        say(f"── targeted refresh: {len(sel)} selector key(s); "
            f"{len(untouched)} unlisted wound(s) LEFT ALONE for their own lane ──")
        for k in untouched[:10]:
            say(f"     (untouched) {k[0]} {k[1]}")

    old_w = sum(w for w, _ in old.values())
    new_w = sum(w for w, _ in proposed.values())
    rises = [(k, old[k][0], proposed[k][0]) for k in sorted(proposed)
             if k in old and proposed[k][0] > old[k][0]]
    added = {k: proposed[k][0] for k in proposed if k not in old}
    removed = {k: old[k][0] for k in old if k not in proposed}

    say(f"── proposed refresh: {old_w} → {new_w} silenced guards "
        f"({len(old)} → {len(proposed)} rows) ──")
    if rises:
        say(f"   rows whose WEIGHT would RISE: {len(rises)}")
        for k, a, b in rises:
            say(f"     +{b - a}  {k[0]} {k[1]}: {a} → {b}")
    if added:
        say(f"   rows that would be ADDED: {len(added)} carrying {sum(added.values())} guards")
        for k in sorted(added, key=lambda x: -added[x])[:10]:
            say(f"     +{added[k]}  {k[0]} {k[1]}")
    if removed:
        say(f"   rows that would be RETIRED: {len(removed)} carrying {sum(removed.values())} guards")
        for k in sorted(removed, key=lambda x: -removed[x])[:10]:
            say(f"     -{removed[k]}  {k[0]} {k[1]}")

    refusals: list[str] = []
    floors = floor_findings(c) if enforce_floors else []
    if floors:
        refusals.append(
            "(d0) the census is VACUOUS — a refresh from a blinded scan would WIPE the ledger "
            "and every arm below would read it as a burndown: " + "; ".join(floors))
    if rises and not allow_increase:
        refusals.append(
            f"(d1) {len(rises)} row(s) would gain WEIGHT — the ratchet only turns DOWN. Root or "
            "discharge those modules, or re-run with `--allow-increase --reason '…'` and say why")
    if new_w > old_w and not allow_increase:
        refusals.append(
            f"(d2) the TOTAL would RISE {old_w} → {new_w} (+{new_w - old_w}) with no row rising "
            "by itself — this is the SPLIT/RENAME shape, where the original's row vanishes and "
            "the pieces enter as new rows arm (c) would even demand. A genuine split's pieces "
            "sum to at most the original")
    if not reason:
        refusals.append(
            "(d3) `--reason` is REQUIRED — a refresh with no recorded reason is exactly the "
            "silent one this gate exists to prevent")
    if unmatched:
        refusals.append(
            "(d3) `--only` selector(s) matched NO baseline row and NO live wound: "
            + ", ".join(repr(s) for s in unmatched)
            + " — a typo'd selector would otherwise write an UNCHANGED ledger carrying a fresh "
              "provenance line that says work was done")

    if refusals:
        say("")
        for r in refusals:
            say(f"REFUSED: {r}")
        say("")
        say("The baseline was NOT written.")
        return 3

    sha, dirty = _head_sha_and_dirt()
    delta = new_w - old_w
    verdict = "INCREASED" if delta > 0 else ("DECREASED" if delta < 0 else "LEVEL")
    if delta == 0 and len(proposed) != len(old):
        verdict = "DECREASED" if len(proposed) < len(old) else "INCREASED"
    prov = read_provenance(path)
    prov.append(f"{PROV_PREFIX} {sha}{'-DIRTY' if dirty else ''} "
                f"W:{old_w}→{new_w} ({delta:+d}) R:{len(old)}→{len(proposed)} "
                f"{verdict} — {reason}")
    write_baseline(path, proposed, prov)
    say(f"wrote {path} — {new_w} silenced guards across {len(proposed)} rows "
        f"[{verdict} {delta:+d}]")
    if verdict == "INCREASED":
        say("⚑ this refresh RAISED the ledger. It is stamped INCREASED in the header and is "
            "greppable; say so in the commit too.")
    return 0


def floor_findings(c: Census) -> list[str]:
    out = []
    if c.dregg2_files < MIN_DREGG2_FILES:
        out.append(f"only {c.dregg2_files} Dregg2/**.lean found (floor {MIN_DREGG2_FILES}) — "
                   f"the corpus moved or the walk broke; this is a blinded scan, not a clean tree")
    if c.guard_modules < MIN_GUARD_MODULES:
        out.append(f"only {c.guard_modules} guard-carrying modules found (floor {MIN_GUARD_MODULES}) — "
                   f"the stripper or the guard regex is broken; a scan this blind cannot report")
    if c.reachable < MIN_REACHABLE:
        out.append(f"only {c.reachable} modules reachable (floor {MIN_REACHABLE}) — "
                   f"the lakefile parse or import BFS is broken; every module would read 'unrooted'")
    return out


# ─────────────────────────────────────────────────────────────────────────────────
# reporting
# ─────────────────────────────────────────────────────────────────────────────────
def print_census(c: Census, label: str) -> None:
    print(f"check-guard-modules [{label}]: {c.dregg2_files} Dregg2/**.lean, "
          f"{c.guard_modules} guard-carrying, {c.reachable} reachable")
    rows = c.rows()
    n_unrooted = sum(1 for k, _ in rows if k == "unrooted")
    n_sorry = sum(1 for k, _ in rows if k == "sorry")
    print(f"  CENSUS: {n_unrooted} unrooted, {n_sorry} sorry-carrying (rooted) — "
          f"{c.total_weight()} guard(s) silenced")


def print_violation_rows(rows: list[tuple[str, str, int, str]], header: str) -> None:
    print(header)
    for kind, module, weight, detail in rows:
        print(f"  {kind.upper():9s} {module}  [{weight}]   ({detail})")


# ─────────────────────────────────────────────────────────────────────────────────
# tree materialisation for --rev
# ─────────────────────────────────────────────────────────────────────────────────
def extract_metatheory(git_root: Path, rev: str, dest: Path) -> Path:
    """git archive <rev> -- metatheory | tar -x. Returns the extracted metatheory dir.
    The working tree is never touched (a churned shared tree is systematically greener
    than HEAD; the census must be judged on the commit)."""
    dest.mkdir(parents=True, exist_ok=True)
    archive = subprocess.Popen(
        ["git", "-C", str(git_root), "archive", rev, "--", "metatheory"],
        stdout=subprocess.PIPE,
    )
    untar = subprocess.Popen(["tar", "-x", "-C", str(dest)], stdin=archive.stdout)
    archive.stdout.close()
    untar.communicate()
    if archive.wait() != 0 or untar.returncode != 0:
        raise RuntimeError(f"git archive {rev} -- metatheory failed")
    return dest / "metatheory"


# ─────────────────────────────────────────────────────────────────────────────────
# the ratchet verdict
# ─────────────────────────────────────────────────────────────────────────────────
def evaluate(c: Census, baseline_path: Path, enforce_floors: bool,
             use_baseline: bool) -> int:
    floors = floor_findings(c) if enforce_floors else []
    live = c.rows()

    fail = False
    if floors:
        fail = True
        print("\ncheck-guard-modules: FAIL — non-vacuity floor(s) tripped (a blinded scan reads as clean):")
        for f in floors:
            print(f"  FLOOR  {f}")

    if not use_baseline:
        # raw census view: every violation fails.
        if live:
            fail = True
            print_violation_rows(
                c.violations(),
                f"\ncheck-guard-modules: {len(live)} guard-carrying module(s) UNROOTED or SORRY "
                f"(each an unrun/vacuous claim):")
        return 1 if fail else 0

    baseline = read_baseline(baseline_path)
    new = sorted(k for k in live if k not in baseline)
    stale = sorted(k for k in baseline if k not in live)
    grew = [(k, baseline[k][0], live[k][0]) for k in sorted(live)
            if k in baseline and live[k][0] > baseline[k][0]]
    shrank = [(k, baseline[k][0], live[k][0]) for k in sorted(live)
              if k in baseline and live[k][0] < baseline[k][0]]

    if new:
        fail = True
        print_violation_rows(
            [(k[0], k[1], live[k][0], live[k][1]) for k in new],
            f"\ncheck-guard-modules: FAIL — {len(new)} NEW guard-carrying module(s) unrooted or "
            f"sorry-carrying, not in the baseline (a guard that never runs / runs below a hole):")
        print("\n  FIX one of:")
        print("    (a) ROOT it — add `import <module>` to metatheory/Dregg2.lean (or an aggregator")
        print("        already imported from there) so `lake build` runs its guards; OR")
        print("    (b) if it carries a sorry, discharge it (a #guard below a sorry is vacuous); OR")
        print(f"    (c) if it is a tracked pre-existing wound, record it — NEVER by hand:")
        print("        check-guard-modules.py --update-baseline --allow-increase \\")
        print("            --only <module> --reason 'why this wound is being tracked'")
        print("        (which stamps INCREASED into the ledger, because it is one)")

    if stale:
        fail = True
        print(f"\ncheck-guard-modules: FAIL — {len(stale)} baseline row(s) are STALE (the wound they "
              f"record is gone — rooted, discharged, or the file was deleted). Retire them with "
              f"`--update-baseline --only <module> --reason '…'`; a stale baseline is how the next "
              f"silent claim gets waved through:")
        for k in stale:
            w, reason = baseline[k]
            print(f"  STALE  {k[0].upper():9s} {k[1]}  [{w}]   (was: {reason or 'no reason given'})")

    if grew:
        fail = True
        print(f"\ncheck-guard-modules: FAIL — {len(grew)} baseline row(s) GAINED weight: the module "
              f"is still unrooted/sorry-carrying and someone added MORE guards to it. Every one of "
              f"them runs in no build:")
        for k, was, now in grew:
            print(f"  GREW   {k[0].upper():9s} {k[1]}: {was} → {now}  (+{now - was})")

    if shrank:
        fail = True
        print(f"\ncheck-guard-modules: FAIL — {len(shrank)} baseline row(s) carry a STALE WEIGHT (the "
              f"wound is still live but smaller). Retire the number with `--update-baseline --only "
              f"<module> --reason '…'` — a ledger that sits above its live weight holds SLACK, and "
              f"slack is what a later refresh spends on new wounds without the total ever rising:")
        for k, was, now in shrank:
            print(f"  STALE-W {k[0].upper():8s} {k[1]}: baseline {was}, actual {now}  (−{was - now})")

    # ⚑ arm (e) — the LEDGER's own integrity, on EVERY ordinary run. Reported after the
    # census so a hand-edit cannot be mistaken for a census finding, and it reds on its own.
    integrity = audit_baseline_integrity(baseline_path)
    if integrity:
        fail = True
        print("\ncheck-guard-modules: FAIL — the BASELINE ITSELF does not add up (a gated refresh "
              "was bypassed; see `--update-baseline`):")
        for f in integrity:
            print(f"  LEDGER  {f}")

    if not fail:
        print(f"\ncheck-guard-modules: PASS — every guard-carrying Dregg2 module is rooted and "
              f"sorry-free, or a tracked baseline wound at its recorded weight; {len(baseline)} "
              f"baseline row(s) carrying {sum(w for w, _ in baseline.values())} silenced guard(s), "
              f"all live, and the ledger adds up.")
    return 1 if fail else 0


# ─────────────────────────────────────────────────────────────────────────────────
# self-test (red-proof) — synthetic tree in a temp dir; working tree never touched
# ─────────────────────────────────────────────────────────────────────────────────
SELFTEST_LAKEFILE = 'name = "Demo"\ndefaultTargets = ["Root"]\n\n[[lean_lib]]\nname = "Root"\n'


def _write(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _build_synthetic(tree: Path) -> Path:
    mt = tree / "metatheory"
    _write(mt / "lakefile.toml", SELFTEST_LAKEFILE)
    # Root.lean roots Good, Sorried and Decoy (imports), NOT Orphan.
    _write(mt / "Root.lean", "import Root.Good\nimport Root.Sorried\nimport Root.Decoy\n")
    # Good: rooted, guard-carrying, sorry-free -> CLEAN control (must NOT be flagged).
    _write(mt / "Root" / "Good.lean",
           "def Root.Good.x : Nat := 1\ntheorem Root.Good.t : x = 1 := rfl\n#assert_axioms Root.Good.t\n")
    # Orphan: guard-carrying (THREE guards -> weight 3), imported by nothing -> UNROOTED.
    _write(mt / "Root" / "Orphan.lean",
           "-- a headline that never runs\n#guard (1 + 1) == 2\n#guard (2 + 2) == 4\n"
           "#assert_axioms Root.Orphan.t\n")
    # Sorried: rooted, guard-carrying, real sorry -> SORRY violation.
    _write(mt / "Root" / "Sorried.lean",
           "theorem Root.Sorried.t : True := by\n  sorry\n#guard true == true\n")
    # A decoy: ROOTED and guard-carrying, but its only sorry/admit tokens are the
    # heavy-identifier `admit` field and the `sorryAx` NAME LITERAL — neither a hole.
    # It must pass BOTH arms (rooted, no real hole).
    _write(mt / "Root" / "Decoy.lean",
           'structure Root.Decoy.S where\n  admit : Int → Int → Bool\n'
           '#guard (#[``sorryAx]).size == 1\n')
    return mt


def run_self_test(git_root: Path) -> int:
    import contextlib
    import io

    print("check-guard-modules: SELF-TEST (red-proof) — synthetic tree in a temp dir;")
    print("  the working tree is never touched by this mode.\n")
    failures = 0
    arms = 0

    def quiet_eval(*a, **k) -> int:
        with contextlib.redirect_stdout(io.StringIO()):
            return evaluate(*a, **k)

    def refresh(bl: Path, c: Census, reason, allow=False, only=None) -> int:
        return refresh_baseline(bl, c, reason, allow, quiet=True, only=only,
                                enforce_floors=False)

    tmp = Path(tempfile.mkdtemp(prefix="guard-modules-self-"))
    try:
        mt = _build_synthetic(tmp)
        c = scan(mt, scope_prefix="Root")
        rows = c.rows()

        def check(name: str, held: bool, detail: str) -> None:
            nonlocal failures, arms
            arms += 1
            if held:
                print(f"  {name:58s} \033[32mok\033[0m    {detail}")
            else:
                print(f"  {name:58s} \033[31mFAIL\033[0m  {detail}")
                failures += 1

        # ── the census arms (a)/(b) and their false-positive controls ──────────────
        check("unrooted guard module flagged", ("unrooted", "Root.Orphan") in rows,
              "Root.Orphan reported UNROOTED")
        check("rooted sorry-carrying guard flagged", ("sorry", "Root.Sorried") in rows,
              "Root.Sorried reported SORRY")
        check("clean rooted guard NOT flagged (control)",
              not any(m == "Root.Good" for _, m in rows),
              "Root.Good absent from violations")
        check("admit-identifier / sorryAx-name-literal NOT a hole",
              not any(m == "Root.Decoy" for _, m in rows),
              "Root.Decoy (rooted, no real hole) absent from violations")
        check("a row's WEIGHT counts the guards the wound silences",
              rows[("unrooted", "Root.Orphan")][0] == 3,
              f"Root.Orphan weight={rows[('unrooted', 'Root.Orphan')][0]} (2 #guard + 1 #assert_axioms)")
        check("several holes in one module are ONE row, not one per hit",
              sum(1 for k in rows if k[0] == "sorry") == 1,
              "Root.Sorried contributes exactly one `sorry` row")
        check("--census verdict is non-zero on violations",
              quiet_eval(c, git_root / "nonexistent", enforce_floors=False, use_baseline=False) == 1,
              "raw census exits 1")

        # ── the ratchet arms against a ledger ─────────────────────────────────────
        bl = tmp / "baseline.txt"
        # ⚑ CREATING a ledger from nothing IS a rise (0 → n) and is refused like any other.
        # That is not pedantry: DELETE-then-RECREATE is otherwise a silent way to relaunder a
        # whole ledger, and this makes the recreate stamp INCREASED like everything else.
        rc = refresh(bl, c, "create the synthetic ledger")
        check("REFUSED (d2): CREATING a ledger from nothing needs --allow-increase",
              rc == 3 and not bl.is_file(),
              f"rc={rc} — delete-and-recreate cannot be a silent relaunder")
        rc = refresh(bl, c, "self-test: record the synthetic census", allow=True)
        check("CONTROL: a gate-written ledger greens its own census",
              rc == 0 and quiet_eval(c, bl, enforce_floors=False, use_baseline=True) == 0,
              f"rc={rc}, then evaluate == 0")
        base_partial = tmp / "base_partial.txt"
        _write(base_partial, "# TOTAL 1 guards across 1 rows\nsorry\tRoot.Sorried\t1\n")
        check("un-baselined new violation -> ratchet RED",
              quiet_eval(c, base_partial, enforce_floors=False, use_baseline=True) == 1,
              "red on a new unrooted guard module")
        base_stale = tmp / "base_stale.txt"
        _write(base_stale, "# TOTAL 5 guards across 3 rows\nunrooted\tRoot.Orphan\t3\n"
                           "sorry\tRoot.Sorried\t1\nunrooted\tRoot.GhostGone\t1\n")
        check("stale baseline row -> ratchet RED",
              quiet_eval(c, base_stale, enforce_floors=False, use_baseline=True) == 1,
              "red on a baseline row whose wound is gone")
        base_low = tmp / "base_low.txt"
        _write(base_low, "# TOTAL 2 guards across 2 rows\nunrooted\tRoot.Orphan\t1\n"
                         "sorry\tRoot.Sorried\t1\n")
        check("a row that GAINED weight -> ratchet RED",
              quiet_eval(c, base_low, enforce_floors=False, use_baseline=True) == 1,
              "red when a tracked orphan accumulates more silent guards")
        base_high = tmp / "base_high.txt"
        _write(base_high, "# TOTAL 10 guards across 2 rows\nunrooted\tRoot.Orphan\t9\n"
                          "sorry\tRoot.Sorried\t1\n")
        check("a row carrying a STALE (too high) weight -> ratchet RED",
              quiet_eval(c, base_high, enforce_floors=False, use_baseline=True) == 1,
              "red on ledger slack — slack is what a later refresh spends")
        check("floors bite an empty (blinded) scan",
              len(floor_findings(Census())) == 3,
              "0 files / 0 guards / 0 reachable all trip their floor")

        # ── ⚑ THE REFRESH GATE (d0/d1/d2/d3) ──────────────────────────────────────
        # `bl` holds the synthetic census exactly. These arms grade a proposed LEDGER
        # against the standing one — the path that did not exist in this tool at all.
        before = bl.read_text(encoding="utf-8")
        rc = refresh(bl, c, None)
        check("REFUSED (d3): a refresh with NO --reason is refused", rc == 3, f"rc={rc}")
        check("(d3) …and the ledger on disk is UNTOUCHED by the refusal",
              bl.read_text(encoding="utf-8") == before, "byte-identical after the refusal")

        _write(mt / "Root" / "Orphan.lean",
               "#guard (1+1) == 2\n#guard (2+2) == 4\n#assert_axioms t\n#guard (3+3) == 6\n")
        c_up = scan(mt, scope_prefix="Root")
        before = bl.read_text(encoding="utf-8")
        rc = refresh(bl, c_up, "trying to bake in a regrowth")
        check("REFUSED (d1): a refresh that RAISES a row's weight is refused", rc == 3, f"rc={rc}")
        check("(d1) …and the ledger on disk is UNTOUCHED by the refusal",
              bl.read_text(encoding="utf-8") == before, "byte-identical after the refusal")

        # (d2) ⚑ THE LAUNDERING SHAPE. Split the tracked orphan into pieces that SUM
        # HIGHER. No row rises (the original's row vanishes, the pieces are new rows),
        # and arm (c) would even DEMAND those new rows exist. Only the TOTAL sees it.
        (mt / "Root" / "Orphan.lean").unlink()
        _write(mt / "Root" / "Orphan1.lean", "#guard (1+1) == 2\n#guard (2+2) == 4\n")
        _write(mt / "Root" / "Orphan2.lean", "#guard (3+3) == 6\n#assert_axioms t\n")
        c_split = scan(mt, scope_prefix="Root")
        base_rows = read_baseline(bl)
        split_rises = [k for k in c_split.rows()
                       if k in base_rows and c_split.rows()[k][0] > base_rows[k][0]]
        check("(d2) the SPLIT raises the total while NO row rises (the shape itself)",
              c_split.total_weight() > sum(w for w, _ in base_rows.values()) and not split_rises,
              f"rises={split_rises}, total "
              f"{sum(w for w, _ in base_rows.values())}→{c_split.total_weight()}")
        rc = refresh(bl, c_split, "split Orphan into Orphan1/Orphan2")
        check("REFUSED (d2): a SPLIT whose pieces sum HIGHER is refused", rc == 3, f"rc={rc}")

        # …and a split whose pieces sum to AT MOST the original is ACCEPTED — the gate
        # blocks laundering, not splitting. (Row COUNT deliberately does not ratchet.)
        _write(mt / "Root" / "Orphan2.lean", "#guard (3+3) == 6\n")
        c_lvl = scan(mt, scope_prefix="Root")
        rc = refresh(bl, c_lvl, "split Orphan into two pieces summing to the original")
        check("CONTROL: a LEVEL split (pieces sum to the original) is ACCEPTED",
              rc == 0 and len(read_baseline(bl)) == 3, f"rc={rc}, rows={len(read_baseline(bl))}")
        check("…and the census is GREEN against the refreshed ledger",
              quiet_eval(c_lvl, bl, enforce_floors=False, use_baseline=True) == 0,
              "evaluate == 0 after an accepted refresh")

        # a legitimate DOWNWARD refresh, and provenance
        (mt / "Root" / "Orphan2.lean").unlink()
        c_down = scan(mt, scope_prefix="Root")
        rc = refresh(bl, c_down, "rooted Orphan2 (it is gone from the census)")
        check("a legitimate DOWNWARD refresh with a reason is ACCEPTED", rc == 0, f"rc={rc}")
        prov = read_provenance(bl)
        check("…and it STAMPED provenance into the header",
              any("DECREASED" in ln and "rooted Orphan2" in ln for ln in prov),
              f"{len(prov)} provenance line(s)")
        check("…and provenance ACCUMULATES (earlier refreshes are still on the record)",
              len(prov) >= 3, f"{len(prov)} provenance line(s)")
        check("…and provenance records the SHA and the tree's dirtiness",
              bool(re.search(r'BASELINE-PROVENANCE \S+ W:\d+', prov[-1])), prov[-1][:90])

        # the override exists, is LOUD, and still needs a reason
        _write(mt / "Root" / "Loud.lean", "#guard 5 == 5\n#guard 6 == 6\n")
        c_loud = scan(mt, scope_prefix="Root")
        rc = refresh(bl, c_loud, None, allow=True)
        check("--allow-increase STILL requires --reason", rc == 3, f"rc={rc}")
        rc = refresh(bl, c_loud, "new orphan, paid for later", allow=True)
        check("--allow-increase with a reason is ACCEPTED", rc == 0, f"rc={rc}")
        check("…and the rise is stamped INCREASED (greppable, never silent)",
              any("INCREASED" in ln for ln in read_provenance(bl)),
              f"{len(read_provenance(bl))} provenance line(s)")

        # (d0) a blinded census must not be able to WIPE the ledger
        before = bl.read_text(encoding="utf-8")
        rc = refresh_baseline(bl, Census(), "wipe it", False, quiet=True, enforce_floors=True)
        check("REFUSED (d0): a refresh from a BLINDED census is refused", rc == 3, f"rc={rc}")
        check("(d0) …and the ledger on disk is UNTOUCHED by that refusal",
              bl.read_text(encoding="utf-8") == before, "byte-identical; the ledger survived")

        # ── ⚑ `--only`: a lane retires ITS rows and cannot absorb a sibling's ──────
        (mt / "Root" / "Loud.lean").unlink()
        c_reset = scan(mt, scope_prefix="Root")
        rc = refresh(bl, c_reset, "reset for the --only arm", allow=True)
        check("setup: ledger holds the lane's row", rc == 0 and ("unrooted", "Root.Orphan1") in read_baseline(bl),
              f"rc={rc}")
        _write(mt / "Root" / "SiblingWip.lean", "#guard 7 == 7\n#guard 8 == 8\n#guard 9 == 9\n")
        (mt / "Root" / "Orphan1.lean").unlink()       # this lane rooted its own module
        c_only = scan(mt, scope_prefix="Root")
        rc = refresh(bl, c_only, "retire Orphan1", only=["Root.Orphan1"])
        after = read_baseline(bl)
        check("--only retires the NAMED row",
              rc == 0 and ("unrooted", "Root.Orphan1") not in after, f"rc={rc}")
        check("⚑ --only does NOT absorb the sibling's unlisted wound",
              ("unrooted", "Root.SiblingWip") not in after, "sibling row absent")
        check("…and the sibling's module still REDS as unlisted (its lane must own it)",
              quiet_eval(c_only, bl, enforce_floors=False, use_baseline=True) == 1,
              "evaluate == 1")
        rc = refresh(bl, c_only, "kind-qualified selector", only=["unrooted:Root.SiblingWip"])
        check("--only accepts a `kind:module` selector",
              rc == 3, f"rc={rc} — refused by (d2), the row would ADD weight")
        rc = refresh(bl, c_only, "kind-qualified selector", allow=True,
                     only=["unrooted:Root.SiblingWip"])
        check("…and with --allow-increase it adopts exactly that one row",
              rc == 0 and ("unrooted", "Root.SiblingWip") in read_baseline(bl), f"rc={rc}")
        _write(mt / "Root" / "SiblingWip.lean", "#guard 7 == 7\n#guard 8 == 8\n"
                                               "#guard 9 == 9\n#guard 10 == 10\n")
        c_grow = scan(mt, scope_prefix="Root")
        rc = refresh(bl, c_grow, "sneak the row back up", only=["Root.SiblingWip"])
        check("--only is STILL subject to (d1)/(d2): it cannot raise its own row",
              rc == 3, f"rc={rc}")
        before = bl.read_text(encoding="utf-8")
        rc = refresh(bl, c_only, "retire a module I misspelled", only=["Root.Orphn1"])
        check("REFUSED (d3): an `--only` selector that matches NOTHING is refused",
              rc == 3 and bl.read_text(encoding="utf-8") == before,
              "a typo must not stamp provenance on an unchanged ledger")
        try:
            parse_selectors(["nosuchkind:Root.Orphan1"])
            bad_kind = False
        except ValueError:
            bad_kind = True
        check("an `--only` selector with an unknown KIND is rejected outright",
              bad_kind, "parse_selectors raises")

        # ── ⚑ ARM (e): the LEDGER checks itself, so an EDITOR cannot route around it ──
        _write(mt / "Root" / "SiblingWip.lean", "#guard 7 == 7\n")
        c_e = scan(mt, scope_prefix="Root")
        rc = refresh(bl, c_e, "clean state for the integrity arm")
        check("setup: a gate-written baseline is self-consistent",
              rc == 0 and not audit_baseline_integrity(bl),
              f"rc={rc} findings={audit_baseline_integrity(bl)}")
        check("…and a surviving row KEEPS its reason column across refreshes",
              all(r for _, r in read_baseline(bl).values()),
              "every row still carries a reason")

        txt = bl.read_text(encoding="utf-8")
        hand = txt.replace("Root.SiblingWip\t1", "Root.SiblingWip\t9")
        check("the hand-edit actually changed a weight", hand != txt, "replacement applied")
        bl.write_text(hand, encoding="utf-8")
        f_e = audit_baseline_integrity(bl)
        check("RED (e): a HAND-RAISED weight is DETECTED (header TOTAL no longer adds up)",
              any("EDITED without going through" in x for x in f_e), f"findings={len(f_e)}")
        check("(e) …and the provenance tail catches it INDEPENDENTLY",
              any("after the last recorded refresh" in x for x in f_e), f"findings={len(f_e)}")
        check("(e) …and an ORDINARY gate run reds on it (not only a refresh)",
              quiet_eval(c_e, bl, enforce_floors=False, use_baseline=True) == 1,
              "evaluate == 1 with a census that would otherwise be green")

        bl.write_text(txt.rstrip("\n") + "\nunrooted\tRoot.PastedIn\t0\n", encoding="utf-8")
        check("RED (e): a HAND-PASTED row is DETECTED (header row count no longer matches)",
              any("added or deleted by hand" in x for x in audit_baseline_integrity(bl)),
              f"findings={len(audit_baseline_integrity(bl))}")

        bl.write_text("unrooted\tRoot.Orphan1\t3\n", encoding="utf-8")
        check("RED (e): a baseline with NO header was not written by the gated refresh",
              any("no `# TOTAL" in x for x in audit_baseline_integrity(bl)),
              f"findings={len(audit_baseline_integrity(bl))}")

        bl.write_text("# TOTAL 3 guards across 1 rows\nunrooted Root.Orphan1  # old format\n",
                      encoding="utf-8")
        check("RED (e): an OLD-FORMAT (weightless) row is refused as unreadable",
              any("CANNOT READ" in x for x in audit_baseline_integrity(bl)),
              f"findings={len(audit_baseline_integrity(bl))}")

        bl.write_text(txt.replace("# TOTAL", "# TOTAL 99 guards across 99 rows\n# TOTAL", 1),
                      encoding="utf-8")
        check("RED (e): a SECOND `# TOTAL` line (forged header) is refused",
              any("`# TOTAL` lines" in x for x in audit_baseline_integrity(bl)),
              f"findings={len(audit_baseline_integrity(bl))}")

        rc = refresh(bl, c_e, "regenerate after the hand-edits", allow=True)
        check("CONTROL: a gate-written refresh RESTORES integrity (a detector, not a trap)",
              rc == 0 and not audit_baseline_integrity(bl),
              f"rc={rc} findings={audit_baseline_integrity(bl)}")
        check("CONTROL: and the census is GREEN again afterwards",
              quiet_eval(c_e, bl, enforce_floors=False, use_baseline=True) == 0,
              "evaluate == 0")
        check("a MISSING baseline file reports no integrity finding (absence is arm (c)'s job)",
              audit_baseline_integrity(tmp / "nope.txt") == [], "no findings for a missing file")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print()
    if failures:
        print(f"check-guard-modules --self-test: FAIL — {failures}/{arms} red-proof assertion(s) "
              f"did not hold")
        return 1
    print(f"check-guard-modules --self-test: {arms}/{arms} red-proof assertions held "
          f"(controls green, faults red)")
    return 0


# ─────────────────────────────────────────────────────────────────────────────────
def main() -> int:
    ap = argparse.ArgumentParser(add_help=True, description="guard-carrying-but-unrooted/sorry census + gate")
    ap.add_argument("--rev", help="scan a clean `git archive` extract of this revision (churn-safe)")
    ap.add_argument("--census", action="store_true", help="ignore the baseline; exit 1 on ANY violation")
    ap.add_argument("--print-census", action="store_true", help="list every violation and exit 0")
    ap.add_argument("--self-test", action="store_true", help="red-proof against a synthetic tree")
    ap.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    ap.add_argument("--update-baseline", action="store_true",
                    help="rewrite the ledger from the current census (retire fixed rows). REFUSES "
                         "to raise any row's weight or the total; requires --reason")
    ap.add_argument("--reason", help="why this refresh happens — stamped into the ledger header "
                                     "with the sha and the tree's dirtiness. Required by "
                                     "--update-baseline")
    ap.add_argument("--allow-increase", action="store_true",
                    help="⚑ permit a refresh that RAISES a row or the total. Still requires "
                         "--reason, and stamps INCREASED into the header")
    ap.add_argument("--only", action="append", metavar="SELECTOR",
                    help="⚑ refresh ONLY these rows (repeatable). `Dregg2.Foo` or "
                         "`unrooted:Dregg2.Foo`. Every other row keeps its standing value — so a "
                         "lane in a shared tree cannot absorb a sibling's in-flight wounds. Use "
                         "this by default")
    ap.add_argument("--metatheory-dir", type=Path, help="override the metatheory dir (testing)")
    args = ap.parse_args()

    root = repo_root()

    if args.self_test:
        return run_self_test(root)

    tmpdir = None
    try:
        if args.rev:
            tmpdir = Path(tempfile.mkdtemp(prefix="guard-modules-rev-"))
            mt = extract_metatheory(root, args.rev, tmpdir)
            label = args.rev
        elif args.metatheory_dir:
            mt = args.metatheory_dir
            label = "override"
        else:
            mt = root / "metatheory"
            label = "working tree"

        if not (mt / "lakefile.toml").is_file():
            print(f"check-guard-modules: FATAL — no lakefile.toml under {mt}", file=sys.stderr)
            return 2
        if not (mt / "Dregg2.lean").is_file():
            print(f"check-guard-modules: FATAL — the Dregg2 lib root is missing: {mt}/Dregg2.lean",
                  file=sys.stderr)
            return 2

        c = scan(mt)
        print_census(c, label)

        if args.print_census:
            print_violation_rows(c.violations(), "\nfull census (every guard-carrying unrooted/sorry module):")
            return 0

        if args.update_baseline:
            return refresh_baseline(args.baseline, c, args.reason, args.allow_increase,
                                    only=args.only)

        return evaluate(c, args.baseline, enforce_floors=True, use_baseline=not args.census)
    except ValueError as e:
        print(f"check-guard-modules: FATAL — {e}", file=sys.stderr)
        return 2
    finally:
        if tmpdir is not None:
            shutil.rmtree(tmpdir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
