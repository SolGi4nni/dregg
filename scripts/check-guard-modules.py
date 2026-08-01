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
  * PRINTS the full census every run — the backlog is visible and named, never buried.
`--census` ignores the baseline and exits non-zero on the RAW census (every violation),
which is the "report every silent claim" view.

═══ USAGE ═════════════════════════════════════════════════════════════════════════
  python3 scripts/check-guard-modules.py                # working tree, ratcheted
  python3 scripts/check-guard-modules.py --rev HEAD      # clean extract of HEAD (churn-safe)
  python3 scripts/check-guard-modules.py --census        # raw census, ignore baseline
  python3 scripts/check-guard-modules.py --print-census  # list every violation, exit 0
  python3 scripts/check-guard-modules.py --self-test     # red-proof (synthetic tree)
Exit: 0 clean/ratchet-green · 1 violation or stale row or vacuous scan · 2 environment error
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
        self.unrooted: list[str] = []              # module
        self.sorry: list[tuple[str, int, str]] = []  # (module, line, token)

    def violations(self) -> list[tuple[str, str, str]]:
        """(kind, module, detail). kind in {"unrooted","sorry"}."""
        rows: list[tuple[str, str, str]] = []
        for m in self.unrooted:
            rows.append(("unrooted", m, "reachable from no default lake target"))
        for m, ln, tok in self.sorry:
            rows.append(("sorry", m, f"carries `{tok}` at line {ln}"))
        return rows


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
        if not carries_guard(stripped):
            continue
        c.guard_modules += 1
        rooted = m in reach
        if not rooted:
            c.unrooted.append(m)
            continue  # sorry arm is scoped to ROOTED modules (unrooted already reported)
        for ln, tok in hole_hits(stripped):
            c.sorry.append((m, ln, tok))
    c.unrooted.sort()
    c.sorry.sort()
    return c


# ─────────────────────────────────────────────────────────────────────────────────
# baseline (burndown ledger)
# ─────────────────────────────────────────────────────────────────────────────────
def read_baseline(path: Path) -> list[tuple[str, str, str]]:
    """Rows `KIND MODULE [# reason]` -> (kind, module, reason). KIND in {unrooted,sorry}."""
    rows: list[tuple[str, str, str]] = []
    if not path.is_file():
        return rows
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        body, _, reason = s.partition("#")
        parts = body.split()
        if len(parts) < 2:
            continue
        kind, module = parts[0].strip(), parts[1].strip()
        rows.append((kind, module, reason.strip()))
    return rows


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
    print(f"  CENSUS: {len(c.unrooted)} unrooted, {len(c.sorry)} sorry-carrying (rooted)")


def print_violation_rows(rows: list[tuple[str, str, str]], header: str) -> None:
    print(header)
    for kind, module, detail in rows:
        print(f"  {kind.upper():9s} {module}   ({detail})")


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
    rows = c.violations()
    row_keys = {(k, m) for k, m, _ in rows}

    fail = False
    if floors:
        fail = True
        print("\ncheck-guard-modules: FAIL — non-vacuity floor(s) tripped (a blinded scan reads as clean):")
        for f in floors:
            print(f"  FLOOR  {f}")

    if not use_baseline:
        # raw census view: every violation fails.
        if rows:
            fail = True
            print_violation_rows(
                rows,
                f"\ncheck-guard-modules: {len(rows)} guard-carrying module(s) UNROOTED or SORRY "
                f"(each an unruns/vacuous claim):")
        return 1 if fail else 0

    baseline = read_baseline(baseline_path)
    base_keys = {(k, m) for k, m, _ in baseline}
    new = sorted(r for r in rows if (r[0], r[1]) not in base_keys)
    stale = sorted(b for b in baseline if (b[0], b[1]) not in row_keys)

    if new:
        fail = True
        print_violation_rows(
            new,
            f"\ncheck-guard-modules: FAIL — {len(new)} NEW guard-carrying module(s) unrooted or "
            f"sorry-carrying, not in the baseline (a guard that never runs / runs below a hole):")
        print("\n  FIX one of:")
        print("    (a) ROOT it — add `import <module>` to metatheory/Dregg2.lean (or an aggregator")
        print("        already imported from there) so `lake build` runs its guards; OR")
        print("    (b) if it carries a sorry, discharge it (a #guard below a sorry is vacuous); OR")
        print(f"    (c) if it is a tracked pre-existing wound, add a row to {baseline_path.name}:")
        print("        <unrooted|sorry> <module>   # why it is not yet rooted/discharged, who owns it")

    if stale:
        fail = True
        print(f"\ncheck-guard-modules: FAIL — {len(stale)} baseline row(s) are STALE (the wound they "
              f"record is gone — rooted, discharged, or the file was deleted). Delete them; a stale "
              f"baseline is how the next silent claim gets waved through:")
        for kind, module, reason in stale:
            print(f"  STALE  {kind.upper():9s} {module}   (was: {reason or 'no reason given'})")

    if not fail:
        print(f"\ncheck-guard-modules: PASS — every guard-carrying Dregg2 module is rooted and "
              f"sorry-free, or a tracked baseline wound; {len(baseline)} baseline row(s), all live.")
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
    # Orphan: guard-carrying, imported by nothing -> UNROOTED violation.
    _write(mt / "Root" / "Orphan.lean",
           "-- a headline that never runs\n#guard (1 + 1) == 2\n")
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

    def quiet_eval(*a, **k) -> int:
        with contextlib.redirect_stdout(io.StringIO()):
            return evaluate(*a, **k)

    tmp = Path(tempfile.mkdtemp(prefix="guard-modules-self-"))
    try:
        mt = _build_synthetic(tmp)
        c = scan(mt, scope_prefix="Root")
        vk = {(k, m) for k, m, _ in c.violations()}

        def check(name: str, held: bool, detail: str) -> None:
            nonlocal failures
            if held:
                print(f"  {name:52s} \033[32mok\033[0m    {detail}")
            else:
                print(f"  {name:52s} \033[31mFAIL\033[0m  {detail}")
                failures += 1

        check("unrooted guard module flagged", ("unrooted", "Root.Orphan") in vk,
              "Root.Orphan reported UNROOTED")
        check("rooted sorry-carrying guard flagged", ("sorry", "Root.Sorried") in vk,
              "Root.Sorried reported SORRY")
        # control: the clean rooted guard module must NOT appear
        check("clean rooted guard NOT flagged (control)",
              not any(m == "Root.Good" for _, m, _ in c.violations()),
              "Root.Good absent from violations")
        # decoy: rooted, and its admit-identifier + sorryAx-name-literal are NOT holes
        check("admit-identifier / sorryAx-name-literal NOT a hole",
              not any(m == "Root.Decoy" for _, m, _ in c.violations()),
              "Root.Decoy (rooted, no real hole) absent from violations")
        # the raw-census verdict must be non-zero (violations exist)
        check("--census verdict is non-zero on violations",
              quiet_eval(c, git_root / "nonexistent", enforce_floors=False, use_baseline=False) == 1,
              "raw census exits 1")

        # ratchet both directions: a baseline covering both -> green; then a new one -> red.
        base_ok = tmp / "base_ok.txt"
        _write(base_ok, "unrooted Root.Orphan\nsorry Root.Sorried\n")
        check("baseline covering the census -> ratchet GREEN",
              quiet_eval(c, base_ok, enforce_floors=False, use_baseline=True) == 0,
              "green (exit 0) when both wounds are baselined")
        base_partial = tmp / "base_partial.txt"
        _write(base_partial, "sorry Root.Sorried\n")  # Orphan now un-baselined -> NEW
        check("un-baselined new violation -> ratchet RED",
              quiet_eval(c, base_partial, enforce_floors=False, use_baseline=True) == 1,
              "red (exit 1) on a new unrooted guard module")
        base_stale = tmp / "base_stale.txt"
        _write(base_stale, "unrooted Root.Orphan\nsorry Root.Sorried\nunrooted Root.GhostGone\n")
        check("stale baseline row -> ratchet RED",
              quiet_eval(c, base_stale, enforce_floors=False, use_baseline=True) == 1,
              "red (exit 1) on a baseline row whose wound is gone")

        # a blinded reader (empty scan) must trip every non-vacuity floor, not read clean.
        empty = Census()
        check("floors bite an empty (blinded) scan",
              len(floor_findings(empty)) == 3,
              "0 files / 0 guards / 0 reachable all trip their floor")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print()
    if failures:
        print(f"check-guard-modules --self-test: FAIL — {failures} red-proof assertion(s) did not hold")
        return 1
    print("check-guard-modules --self-test: all red-proof assertions held (control green, faults red)")
    return 0


# ─────────────────────────────────────────────────────────────────────────────────
def main() -> int:
    ap = argparse.ArgumentParser(add_help=True, description="guard-carrying-but-unrooted/sorry census + gate")
    ap.add_argument("--rev", help="scan a clean `git archive` extract of this revision (churn-safe)")
    ap.add_argument("--census", action="store_true", help="ignore the baseline; exit 1 on ANY violation")
    ap.add_argument("--print-census", action="store_true", help="list every violation and exit 0")
    ap.add_argument("--self-test", action="store_true", help="red-proof against a synthetic tree")
    ap.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
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

        return evaluate(c, args.baseline, enforce_floors=True, use_baseline=not args.census)
    finally:
        if tmpdir is not None:
            shutil.rmtree(tmpdir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
