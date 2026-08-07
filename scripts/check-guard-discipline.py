#!/usr/bin/env python3
"""check-guard-discipline.py — the `#guard` population may only RATCHET DOWN, per module.

═══ THE ARGUMENT, STATED SO THE GATE IS OBVIOUSLY THE RIGHT SHAPE ═════════════════
`#guard e` evaluates ONE closed instance at elaboration time. It proves nothing about all
inputs, PRODUCES NO TERM anything can build on, and is invisible to axiom accounting.
Measured 2026-08-02 over `metatheory/**/*.lean` (comments and string literals stripped):
**15,850 `#guard`s in 1,159 files**, of which `Dregg2/Circuit/Emit/KimchiStepMain.lean`
alone holds 838.

⚑ AND IT IS NOT EVEN A CHEAPER CHECK. Lean 4.30, `Lean/Elab/Tactic/Guard.lean:154-167`:

    let v ← unsafe evalExpr (checkMeta := false) Bool (mkConst ``Bool) e

`#guard` runs the **unsafe compiled evaluator** — the same engine `native_decide` runs on.
So `#guard e` is exactly `theorem _ : e = true := by native_decide` with THREE things
deleted: the NAME (nothing can cite it), the TERM (nothing can compose on it), and the
AXIOM RECORD (`collectAxioms` sees nothing, so `#assert_axioms` is structurally blind to
it). A `#guard` does not avoid trusting the compiler. It trusts the compiler SILENTLY.

This is the sin `CLAUDE.md` already forbids in the other language — "a Rust test that 'the
AIR accepts iff applyTurn holds' on cases is just unit tests with ZERO formal content" —
and moving case-tests into Lean did not make them verification.

Policy: `metatheory/docs/GUARD-DISCIPLINE.md`. **A fact worth asserting is worth naming.**

═══ WHAT THIS GATE DOES, AND WHY IT IS A RATCHET AND NOT A BAN ════════════════════
15,850 cannot go to zero in one pass, and a flat ban would be a gate nobody can keep
green — which is the same as no gate. So: a PER-MODULE baseline in
`scripts/guard-discipline-baseline.txt` that may only SHRINK. Three red paths:

  (a) ABOVE baseline — a module gained guards. In a module someone already converted, a
      new `#guard` is a regression to the habit; this is the arm that stops the bleed.
  (b) BELOW baseline — a STALE ROW. You converted guards and did not retire the number.
      Same shape `check-guard-modules.py` uses: fixing a module FORCES retiring its row,
      which is what makes the census monotone rather than merely non-increasing.
  (c) UNLISTED and carrying guards — a NEW guard-carrying module. The population cannot
      grow sideways into files the baseline never saw.

⚠ WHAT THIS DOES NOT CATCH — read before trusting a green:
  * WHICH guards remain. A module at its baseline may hold its most load-bearing pin as a
    `#guard` forever. This gate bounds the COUNT; it does not read what any guard claims.
  * A guard converted to a VACUOUS theorem. `theorem t : True := trivial` shrinks the count
    and asserts nothing. That is semantic vacuity — `#assert_axioms`/`#assert_compiled` and
    an adversarial reader, not a counter.
  * A guard DELETED rather than converted. The count falls either way. Deletion is
    sometimes right (a throwaway sanity check nothing cites) and sometimes an assertion
    lost; only the diff says which.
  * Anything about `#assert_axioms` / `#assert_namespace_axioms`, which are NOT counted
    here — those produce no term either, but they are pins ON named theorems and are the
    instrument this policy pushes work TOWARD. Counting them would point the ratchet
    backwards. `check-guard-modules.py` is the gate that they actually run.

═══ ⚑⚑ THE REFRESH GATE — measured 2026-08-02, and it is why this file has arm (d) ══
Every arm above guards the CENSUS against the BASELINE. Nothing guarded the BASELINE
itself, and `--update-baseline` rewrote it unconditionally. So the ratchet could be turned
UP by the one operation that exists to turn it down, and a green afterwards certified the
new number rather than the old one.

⚑ IT ALREADY HAPPENED, AND NOT IN THE SHAPE ANYONE WATCHES FOR. Every baseline commit,
graded by the gate below:

    a7d30783d  CREATE  15,656 across 1,156 rows
    935d8ef09  15,656 → 15,679  (+23)   rows_up=0  added=837  removed=814   ⚑ REFUSED (d2)
    a819016de  15,679 → 15,665  (−14)   rows_up=0  added=0    removed=0     — honest

`935d8ef09` is the module SPLIT, and it rewrote the ledger IN THE SAME COMMIT: it removed
`Dregg2/Circuit/Emit/KimchiStepMain.lean` (814) and added thirteen `…Pins01–13` rows
totalling **837**. **No row was raised.** Twenty-three guards the same commit had just
written entered the baseline as two operations that each look correct on their own — a
burned-down module retiring its row, and arm (c) being obeyed by giving new guard-carrying
modules their rows. Both arms were satisfied at every step.

⚠ AND THE NEXT REFRESH HID IT FURTHER. `a819016de` was an HONEST −14 (a real burndown in
`MinaMultiBlockConformance`, 49 → 35). So an auditor reading the two-commit window sees
15,656 → 15,665 — **net +9** — and reads it as noise. A genuine conversion landed on top of
a laundered growth and made it unreadable.

A rename is how a population grows without any row growing, and only the TOTAL can see it.

So the refresh is now itself gated, on three things:

  (d1) **no surviving row may RISE** — the in-place shape of the same sin;
  (d2) **the TOTAL may not rise** — which is what catches a split/rename, since the pieces
       of a genuine split sum to at most the original;
  (d3) **every refresh records PROVENANCE** — sha, dirtiness, totals, and a `--reason`
       written into the baseline header. A refresh from a DIRTY tree is recorded as dirty,
       because that is what the laundered one was: a lane refreshing from its own churn.

⚠ AND THE OVERRIDE IS DELIBERATELY LOUD, NOT ABSENT. `--allow-increase` exists, and it
still requires `--reason`, and it stamps `INCREASED` with the delta into the header. A ban
with no escape hatch gets routed around by hand-editing the file, which is the silent
outcome this gate exists to prevent. The wound was never that the number went up. It was
that nothing said so.

═══ USAGE ═════════════════════════════════════════════════════════════════════════
  python3 scripts/check-guard-discipline.py                 # working tree, ratcheted
  python3 scripts/check-guard-discipline.py --rev HEAD      # clean extract of HEAD (churn-safe)
  python3 scripts/check-guard-discipline.py --top 25        # + the worst offenders
  python3 scripts/check-guard-discipline.py --update-baseline --reason "converted N in <module>"
  python3 scripts/check-guard-discipline.py --update-baseline --allow-increase --reason "..."
  python3 scripts/check-guard-discipline.py --self-test     # red-proof (synthetic tree)
Exit: 0 ratchet-green · 1 violation or stale row or vacuous scan · 2 environment error
       3 REFUSED refresh (the baseline would have risen)
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# The strip_lean_noise lexer is shared with check-guard-modules.py — ONE definition of
# "what the source actually says", so the two censuses cannot drift on tokenisation.
_HERE = Path(__file__).resolve().parent


def _load_sibling_stripper():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "_cgm", str(_HERE / "check-guard-modules.py"))
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load check-guard-modules.py (the shared Lean stripper)")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.strip_lean_noise


strip_lean_noise = _load_sibling_stripper()

import re  # noqa: E402  (after the sibling load, deliberately)

# `#guard` ONLY. `#guard_msgs` is a different command and is excluded by the lookahead;
# `#assert_axioms` is deliberately NOT counted (see the header's "does not catch").
GUARD_RE = re.compile(r'#guard(?![A-Za-z0-9_])')

IGNORE_DIRS = {".lake", ".git", "build", "__pycache__", "wip"}

# ── non-vacuity floors. A scan that finds far fewer than the corpus carries has a broken
# stripper/extract and must FAIL rather than green having counted nothing. Measured at the
# commit that added this gate: 15,850 guards across 1,159 files. ─────────────────────
MIN_FILES_SCANNED = 900
MIN_GUARDS_FOUND = 10000


def repo_root() -> Path:
    try:
        out = subprocess.run(
            ["git", "-C", str(_HERE), "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True)
        return Path(out.stdout.strip())
    except Exception:
        return _HERE.parent


DEFAULT_BASELINE = repo_root() / "scripts" / "guard-discipline-baseline.txt"


def scan(mt: Path) -> tuple[dict[str, int], int]:
    """{relative lean path -> #guard count}, and the number of .lean files scanned."""
    counts: dict[str, int] = {}
    n_files = 0
    for p in sorted(mt.rglob("*.lean")):
        if any(part in IGNORE_DIRS for part in p.relative_to(mt).parts):
            continue
        n_files += 1
        try:
            text = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        n = len(GUARD_RE.findall(strip_lean_noise(text)))
        if n:
            counts[str(p.relative_to(mt))] = n
    return counts, n_files


def audit_baseline_integrity(path: Path) -> list[str]:
    """⚑ THE LEDGER CHECKS ITSELF, so the refresh gate cannot be walked around with an editor.

    (d1)/(d2)/(d3) live in `refresh_baseline`, which is a TOOL — and a tool is only a gate for
    the people who run it. Nothing stops an editor from typing a row upward. What DOES stop it
    being silent: the header carries `# TOTAL <n>`, and the last `BASELINE-PROVENANCE` line
    carries the total that refresh produced. Both must equal the sum of the rows. A hand-edit
    that raises a row and does not forge two more numbers is DETECTED at gate time, by anyone
    running the gate, without needing the history."""
    if not path.exists():
        return []
    rows = read_baseline(path)
    total = sum(rows.values())
    text = path.read_text(encoding="utf-8")
    findings: list[str] = []

    m = re.search(r'^#\s*TOTAL\s+(\d+)\s+guards', text, re.MULTILINE)
    if m is None:
        findings.append("the baseline header has no `# TOTAL <n> guards` line — it was not "
                        "written by the gated refresh")
    elif int(m.group(1)) != total:
        findings.append(
            f"the baseline header says TOTAL {m.group(1)} but its rows sum to {total} "
            f"({total - int(m.group(1)):+d}) — the ledger was EDITED without going through "
            "`--update-baseline`, which is the one path that records why")

    prov = read_provenance(path)
    if prov:
        pm = re.search(r'(\d+)\s*(?:→|->)\s*(\d+)', prov[-1])
        if pm and int(pm.group(2)) != total:
            findings.append(
                f"the last BASELINE-PROVENANCE line ends at {pm.group(2)} but the rows sum to "
                f"{total} — a row moved after the last recorded refresh")
    return findings


def read_baseline(path: Path) -> dict[str, int]:
    if not path.exists():
        return {}
    out: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.rsplit(None, 1) if "\t" not in line else line.split("\t")
        if len(parts) != 2:
            continue
        a, b = (x.strip() for x in parts)
        # tolerate either "count<TAB>path" or "path<TAB>count"
        if a.isdigit():
            out[b] = int(a)
        elif b.isdigit():
            out[a] = int(b)
    return out


PROV_PREFIX = "# BASELINE-PROVENANCE"


def read_provenance(path: Path) -> list[str]:
    """The refresh log carried in the baseline header, oldest first."""
    if not path.exists():
        return []
    return [ln.rstrip() for ln in path.read_text(encoding="utf-8").splitlines()
            if ln.startswith(PROV_PREFIX)]


def _head_sha_and_dirt() -> tuple[str, bool]:
    """(sha, tree-is-dirty). ⚑ Dirtiness is RECORDED, not refused: the laundered refresh of
    2026-08-02 was a lane rewriting the ledger from its own uncommitted churn, so 'which tree
    did this number come from' is the question the header has to be able to answer."""
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


def write_baseline(path: Path, counts: dict[str, int], total_files: int,
                   provenance: list[str] | None = None) -> None:
    total = sum(counts.values())
    lines = [
        "# guard-discipline-baseline.txt — per-module `#guard` counts. A BURNDOWN LEDGER.",
        "# The gate (scripts/check-guard-discipline.py) reds when a module goes ABOVE its row,",
        "# BELOW it (a stale row — retire the number when you convert), or carries guards with",
        "# no row at all. So this file may only ever SHRINK. Policy: metatheory/docs/GUARD-DISCIPLINE.md.",
        "#",
        "# ⚑ A REFRESH IS ITSELF GATED. `--update-baseline` REFUSES to raise any row or the TOTAL",
        "# (the total is what catches a module SPLIT, which grows the population while no row grows —",
        "# that is how 23 guards entered this file on 2026-08-02). Raising it at all requires",
        "# `--allow-increase --reason`, and stamps an INCREASED line below. Never hand-edit a row up:",
        "# the whole point is that every rise is attributable.",
        f"# TOTAL {total} guards across {len(counts)} modules ({total_files} .lean files scanned).",
        "# format: <count><TAB><path relative to metatheory/>",
    ]
    lines.extend(provenance or [])
    lines.append("")
    for p in sorted(counts):
        lines.append(f"{counts[p]}\t{p}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def refresh_baseline(path: Path, counts: dict[str, int], n_files: int,
                     reason: str | None, allow_increase: bool,
                     quiet: bool = False, only: list[str] | None = None) -> int:
    """⚑ THE REFRESH GATE. Returns 0 on a written baseline, 3 on a REFUSED one.

    Arms (d1) no row may rise, (d2) the total may not rise, (d3) provenance is mandatory.
    Kept separate from `evaluate` on purpose: `evaluate` grades a census against a ledger,
    this grades a proposed LEDGER against the standing one, and conflating them is exactly
    how the refresh path ended up ungated.

    ⚑ `only` is the SWARM primitive, and it is not a convenience. The tree is shared: when a
    lane converts guards in three modules, a whole-census refresh would also absorb every
    OTHER lane's in-flight guard-carrying module — which is the laundering shape again, just
    with someone else's work as the payload. `--only` retires exactly the rows a lane earned
    and leaves every other row at its standing value, so a lane can never bake in a number it
    did not produce. The d1/d2 arms still apply to the resulting ledger."""
    def say(*a):
        if not quiet:
            print(*a)

    old = read_baseline(path)
    if only is not None:
        sel = set(only)
        merged = dict(old)
        for p in sel:
            if p in counts:
                merged[p] = counts[p]
            else:
                merged.pop(p, None)
        untouched = sorted(p for p in counts if p not in old and p not in sel)
        counts = merged
        say(f"── targeted refresh: {len(sel)} row(s) named; "
            f"{len(untouched)} unlisted guard-carrying module(s) LEFT ALONE ──")
        for p in untouched[:10]:
            say(f"     (untouched) {p}")
    old_total, new_total = sum(old.values()), sum(counts.values())
    rises = [(p, old[p], counts[p]) for p in sorted(counts)
             if p in old and counts[p] > old[p]]
    added = {p: n for p, n in counts.items() if p not in old}

    say(f"── proposed refresh: {old_total} → {new_total} guards "
        f"({len(old)} → {len(counts)} rows) ──")
    if rises:
        say(f"   rows that would RISE: {len(rises)}")
        for p, a, b in rises:
            say(f"     +{b - a}  {p}: {a} → {b}")
    if added:
        say(f"   rows that would be ADDED: {len(added)} carrying {sum(added.values())} guards")
        for p in sorted(added, key=lambda k: -added[k])[:10]:
            say(f"     +{added[p]}  {p}")

    refusals: list[str] = []
    if rises and not allow_increase:
        refusals.append(
            f"(d1) {len(rises)} row(s) would RISE — the ratchet only turns DOWN. Convert or "
            "delete those guards, or re-run with `--allow-increase --reason '…'` and say why")
    if new_total > old_total and not allow_increase:
        refusals.append(
            f"(d2) the TOTAL would RISE {old_total} → {new_total} (+{new_total - old_total}) "
            "with no row rising by itself — this is the SPLIT/RENAME shape that laundered 23 "
            "guards on 2026-08-02. A genuine split's pieces sum to at most the original")
    if not reason:
        refusals.append(
            "(d3) `--reason` is REQUIRED — a refresh with no recorded reason is exactly the "
            "silent one this gate exists to prevent")

    if refusals:
        say("")
        for r in refusals:
            say(f"REFUSED: {r}")
        say("")
        say("The baseline was NOT written.")
        return 3

    sha, dirty = _head_sha_and_dirt()
    delta = new_total - old_total
    verdict = "INCREASED" if delta > 0 else ("DECREASED" if delta < 0 else "LEVEL")
    prov = read_provenance(path)
    prov.append(
        f"{PROV_PREFIX} {sha}{'-DIRTY' if dirty else ''} {old_total}→{new_total} "
        f"({delta:+d}) {verdict} — {reason}")
    write_baseline(path, counts, n_files, prov)
    say(f"wrote {path} — {new_total} guards across {len(counts)} modules  [{verdict} {delta:+d}]")
    if verdict == "INCREASED":
        say("⚑ this refresh RAISED the ledger. It is stamped INCREASED in the header and is "
            "greppable; say so in the commit too.")
    return 0


def evaluate(counts: dict[str, int], n_files: int, baseline: dict[str, int],
             enforce_floors: bool, label: str, top: int, quiet: bool = False) -> int:
    def say(*a):
        if not quiet:
            print(*a)

    total = sum(counts.values())
    say(f"── guard-discipline census [{label}] ──")
    say(f"   {total} `#guard`s across {len(counts)} modules ({n_files} .lean files scanned)")
    if baseline:
        say(f"   baseline: {sum(baseline.values())} across {len(baseline)} modules")

    findings: list[str] = []
    if enforce_floors:
        if n_files < MIN_FILES_SCANNED:
            findings.append(
                f"VACUOUS SCAN: {n_files} .lean files scanned, floor is {MIN_FILES_SCANNED} "
                "— the extract or the walk is broken; a green here checked nothing")
        if total < MIN_GUARDS_FOUND:
            findings.append(
                f"VACUOUS SCAN: {total} guards found, floor is {MIN_GUARDS_FOUND} "
                "— the stripper or the regex is broken; a green here checked nothing")

    grew: list[tuple[str, int, int]] = []
    stale: list[tuple[str, int, int]] = []
    unlisted: list[tuple[str, int]] = []
    for p, n in sorted(counts.items()):
        if p not in baseline:
            unlisted.append((p, n))
        elif n > baseline[p]:
            grew.append((p, baseline[p], n))
        elif n < baseline[p]:
            stale.append((p, baseline[p], n))
    for p, n in sorted(baseline.items()):
        if p not in counts:
            stale.append((p, n, 0))

    if grew:
        say("")
        say("⚑ RED — a module gained `#guard`s (the ratchet only turns DOWN):")
        for p, was, now in grew:
            say(f"   {p}: {was} → {now}  (+{now - was})")
        findings.append(f"{len(grew)} module(s) ABOVE baseline")
    if unlisted:
        say("")
        say("⚑ RED — guard-carrying module with NO baseline row (population grew sideways):")
        for p, n in unlisted:
            say(f"   {p}: {n}")
        findings.append(f"{len(unlisted)} unlisted guard-carrying module(s)")
    if stale:
        say("")
        say("⚑ RED — STALE baseline row (you converted; retire the number with "
            "`--update-baseline`):")
        for p, was, now in stale:
            say(f"   {p}: baseline {was}, actual {now}  (−{was - now})")
        findings.append(f"{len(stale)} stale baseline row(s)")

    if top:
        say("")
        say(f"── the {top} heaviest modules (the burndown queue) ──")
        for p, n in sorted(counts.items(), key=lambda kv: -kv[1])[:top]:
            say(f"   {n:6d}  {p}")

    say("")
    if findings:
        for f in findings:
            say(f"FAIL: {f}")
        return 1
    say("PASS: guard-discipline ratchet green.")
    return 0


def extract_metatheory(git_root: Path, rev: str, dest: Path) -> Path:
    ar = subprocess.run(["git", "-C", str(git_root), "archive", rev, "--", "metatheory"],
                        capture_output=True)
    if ar.returncode != 0:
        raise RuntimeError(f"git archive {rev} -- metatheory failed: "
                           f"{ar.stderr.decode(errors='replace')[:400]}")
    tar = subprocess.run(["tar", "-x", "-C", str(dest)], input=ar.stdout, capture_output=True)
    if tar.returncode != 0:
        raise RuntimeError("tar -x of the git archive failed")
    return dest / "metatheory"


# ═══ RED-PROOF ═════════════════════════════════════════════════════════════════════
# The headline is a NEGATIVE assertion ("no module gained a guard"), which passes just as
# happily on a broken reader. Every arm is exercised against a synthetic tree; the working
# tree is never touched. Floors are disabled for the synthetic (it is deliberately tiny) —
# and the floors themselves get their own blinded-scan arm.

def _mk(tree: Path, rel: str, body: str) -> None:
    p = tree / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8")


def run_self_test() -> int:
    tmp = Path(tempfile.mkdtemp(prefix="guard-discipline-selftest-"))
    ok = True

    def check(name: str, held: bool, detail: str) -> None:
        nonlocal ok
        print(f"   {'PASS' if held else 'FAIL'}  {name}")
        if not held:
            ok = False
            print(f"         {detail}")

    try:
        mt = tmp / "metatheory"
        _mk(mt, "A.lean", "#guard 1 == 1\n#guard 2 == 2\n")
        _mk(mt, "sub/B.lean", "theorem t : 1 = 1 := rfl\n#guard 3 == 3\n")
        _mk(mt, "sub/Clean.lean", "theorem u : 2 = 2 := rfl\n")
        # comment/string false-positive controls
        _mk(mt, "Prose.lean", '/- we constantly emit shitty #guard s -/\ndef s := "#guard x"\n')
        # #assert_axioms and #guard_msgs must NOT be counted
        _mk(mt, "NotAGuard.lean", "#assert_axioms t\n#guard_msgs in\n#eval 1\n")

        bl = tmp / "baseline.txt"
        counts, nf = scan(mt)

        check("counts only real #guard (comments/strings/#assert_axioms/#guard_msgs excluded)",
              counts == {"A.lean": 2, "sub/B.lean": 1},
              f"got {counts}")

        write_baseline(bl, counts, nf)
        rc = evaluate(counts, nf, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("CONTROL: tree at its own baseline is GREEN", rc == 0, f"rc={rc}")

        # (a) ABOVE baseline
        _mk(mt, "A.lean", "#guard 1 == 1\n#guard 2 == 2\n#guard 4 == 4\n")
        c2, n2 = scan(mt)
        rc = evaluate(c2, n2, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("RED (a): a module that GAINED a guard fails", rc == 1, f"rc={rc}")

        # (b) BELOW baseline — a stale row
        _mk(mt, "A.lean", "#guard 1 == 1\n")
        c3, n3 = scan(mt)
        rc = evaluate(c3, n3, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("RED (b): a CONVERTED module with a stale row fails", rc == 1, f"rc={rc}")

        # (b') a module that lost its file entirely is also stale
        (mt / "A.lean").unlink()
        c3b, n3b = scan(mt)
        rc = evaluate(c3b, n3b, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("RED (b'): a DELETED baselined module fails as stale", rc == 1, f"rc={rc}")

        # (c) UNLISTED guard-carrying module
        _mk(mt, "A.lean", "#guard 1 == 1\n#guard 2 == 2\n")
        _mk(mt, "sub/New.lean", "#guard 9 == 9\n")
        c4, n4 = scan(mt)
        rc = evaluate(c4, n4, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("RED (c): a NEW guard-carrying module with no row fails", rc == 1, f"rc={rc}")

        # baseline update retires the rows and re-greens
        (mt / "sub/New.lean").unlink()
        c5, n5 = scan(mt)
        rc = refresh_baseline(bl, c5, n5, "self-test retire", False, quiet=True)
        check("--update-baseline retires the rows and re-greens", rc == 0, f"rc={rc}")
        rc = evaluate(c5, n5, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("…and the retired baseline greens the census", rc == 0, f"rc={rc}")

        # the ratchet is one-way: the retired (smaller) baseline now REJECTS a regrowth
        _mk(mt, "A.lean", "#guard 1 == 1\n#guard 2 == 2\n#guard 3 == 3\n")
        c6, n6 = scan(mt)
        rc = evaluate(c6, n6, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("the ratchet is ONE-WAY: regrowth past the retired row fails", rc == 1, f"rc={rc}")

        # ── ⚑ THE REFRESH GATE (arms d1/d2/d3) ────────────────────────────────────
        # The census arms above all grade a tree against the ledger. These grade a proposed
        # LEDGER against the standing one — the path that was ungated until 2026-08-02.
        # `bl` currently holds {A:2, sub/B:1}; the tree currently holds A at 3 (the regrowth
        # the arm above just proved reds).

        # (d1) a refresh that would RAISE a row is REFUSED, even with a reason.
        c7, n7 = scan(mt)          # A.lean == 3, above its row of 2
        before = bl.read_text(encoding="utf-8")
        rc = refresh_baseline(bl, c7, n7, "trying to bake in a regrowth", False, quiet=True)
        check("REFUSED (d1): a refresh that RAISES a row is refused", rc == 3, f"rc={rc}")
        check("(d1) …and the baseline on disk is UNTOUCHED by the refusal",
              bl.read_text(encoding="utf-8") == before, "the file was rewritten anyway")

        # (d2) ⚑ THE MEASURED SHAPE. Split a baselined module into pieces that SUM HIGHER.
        # No row rises (the original's row vanishes, the pieces are new rows), and arm (c)
        # would even DEMAND those new rows exist. Only the TOTAL sees it.
        _mk(mt, "A.lean", "#guard 1 == 1\n#guard 2 == 2\n")     # back to its row of 2
        c8, n8 = scan(mt)
        rc = refresh_baseline(bl, c8, n8, "restore", False, quiet=True)
        check("CONTROL: a LEVEL refresh is accepted", rc == 0, f"rc={rc}")
        (mt / "sub/B.lean").unlink()                             # the 1-guard module, "split"…
        _mk(mt, "sub/B1.lean", "#guard 3 == 3\n")                # …into two pieces summing to 2
        _mk(mt, "sub/B2.lean", "#guard 4 == 4\n")
        c9, n9 = scan(mt)
        split_rises = [p for p in c9 if p in read_baseline(bl) and c9[p] > read_baseline(bl)[p]]
        check("(d2) the SPLIT raises the total while NO row rises (the shape itself)",
              sum(c9.values()) > sum(read_baseline(bl).values()) and not split_rises,
              f"rises={split_rises}, total {sum(read_baseline(bl).values())}→{sum(c9.values())}")
        rc = refresh_baseline(bl, c9, n9, "split B into B1/B2", False, quiet=True)
        check("REFUSED (d2): a SPLIT whose pieces sum HIGHER is refused", rc == 3, f"rc={rc}")

        # …and a split whose pieces sum to AT MOST the original still passes — the gate blocks
        # laundering, not splitting.
        (mt / "sub/B2.lean").unlink()
        c10, n10 = scan(mt)
        rc = refresh_baseline(bl, c10, n10, "split B into B1 alone", False, quiet=True)
        check("a LEVEL split (pieces sum to the original) is ACCEPTED", rc == 0, f"rc={rc}")

        # (d3) provenance is mandatory, and it is RECORDED.
        (mt / "A.lean").write_text("#guard 1 == 1\n", encoding="utf-8")   # a real burndown
        c11, n11 = scan(mt)
        rc = refresh_baseline(bl, c11, n11, None, False, quiet=True)
        check("REFUSED (d3): a refresh with NO --reason is refused", rc == 3, f"rc={rc}")
        rc = refresh_baseline(bl, c11, n11, "converted A's second guard", False, quiet=True)
        check("a legitimate DOWNWARD refresh with a reason is ACCEPTED", rc == 0, f"rc={rc}")
        prov = read_provenance(bl)
        check("…and it STAMPED provenance into the header",
              any("DECREASED" in ln and "converted A's second guard" in ln for ln in prov),
              f"provenance={prov}")
        check("…and provenance ACCUMULATES (earlier refreshes are still on the record)",
              len(prov) >= 3, f"{len(prov)} provenance line(s)")

        # the override exists, is LOUD, and still needs a reason.
        _mk(mt, "sub/Loud.lean", "#guard 5 == 5\n#guard 6 == 6\n")
        c12, n12 = scan(mt)
        rc = refresh_baseline(bl, c12, n12, None, True, quiet=True)
        check("--allow-increase STILL requires --reason", rc == 3, f"rc={rc}")
        rc = refresh_baseline(bl, c12, n12, "new module, paid for later", True, quiet=True)
        check("--allow-increase with a reason is ACCEPTED", rc == 0, f"rc={rc}")
        check("…and the rise is stamped INCREASED (greppable, never silent)",
              any("INCREASED" in ln for ln in read_provenance(bl)),
              f"provenance={read_provenance(bl)}")

        # ── ⚑ `--only`: a lane retires ITS rows and cannot absorb a sibling's ─────────
        # The shared-tree shape: this lane converted a guard in A.lean while a SIBLING lane
        # has an unlisted, guard-carrying module in flight. A whole-census refresh would bake
        # the sibling's guards into the ledger — the laundering shape with someone else's work
        # as the payload. `--only A.lean` must retire A's row and leave the sibling alone.
        (mt / "sub/Loud.lean").unlink()
        _mk(mt, "A.lean", "#guard 1 == 1\n")
        c13, n13 = scan(mt)
        rc = refresh_baseline(bl, c13, n13, "reset for the --only arm", True, quiet=True)
        check("setup: ledger holds A at 1", rc == 0 and read_baseline(bl).get("A.lean") == 1,
              f"rc={rc} row={read_baseline(bl).get('A.lean')}")
        _mk(mt, "sub/SiblingWip.lean", "#guard 7 == 7\n#guard 8 == 8\n#guard 9 == 9\n")
        (mt / "A.lean").write_text("", encoding="utf-8")   # this lane converted A's last guard
        c14, n14 = scan(mt)
        rc = refresh_baseline(bl, c14, n14, "retire A", False, quiet=True, only=["A.lean"])
        after = read_baseline(bl)
        check("--only retires the NAMED row", rc == 0 and "A.lean" not in after,
              f"rc={rc}, A.lean={after.get('A.lean')}")
        check("⚑ --only does NOT absorb the sibling's unlisted module",
              "sub/SiblingWip.lean" not in after, f"sibling row={after.get('sub/SiblingWip.lean')}")
        rc = evaluate(c14, n14, after, False, "self-test", 0, quiet=True)
        check("…and the sibling's module still REDS as unlisted (its lane must own it)",
              rc == 1, f"rc={rc}")
        # …and --only is still subject to (d1): it cannot raise the row it names either.
        _mk(mt, "A.lean", "#guard 1 == 1\n#guard 2 == 2\n")
        rc = refresh_baseline(bl, *scan(mt), "sneak A back up", False, quiet=True,
                              only=["A.lean"])
        check("--only is STILL subject to (d1)/(d2): it cannot raise its own row",
              rc == 3, f"rc={rc}")

        # ── ⚑ arm (e): the LEDGER checks itself, so an EDITOR cannot walk around the tool ──
        _mk(mt, "A.lean", "#guard 1 == 1\n")
        c15, n15 = scan(mt)
        rc = refresh_baseline(bl, c15, n15, "clean state for the integrity arm", True, quiet=True)
        check("setup: a gate-written baseline is self-consistent",
              rc == 0 and not audit_baseline_integrity(bl),
              f"rc={rc} findings={audit_baseline_integrity(bl)}")
        # hand-edit a row UPWARD without touching the header — the editor's shortcut
        txt = bl.read_text(encoding="utf-8")
        hand = txt.replace("1\tA.lean", "9\tA.lean")
        check("the hand-edit actually changed a row", hand != txt, "replacement did not apply")
        bl.write_text(hand, encoding="utf-8")
        f_e = audit_baseline_integrity(bl)
        check("RED (e): a HAND-RAISED row is DETECTED (header TOTAL no longer adds up)",
              any("EDITED without going through" in x for x in f_e), f"findings={f_e}")
        check("(e) …and the provenance tail is caught too (a row moved after the last refresh)",
              any("after the last recorded refresh" in x for x in f_e), f"findings={f_e}")
        # …and a header with no TOTAL at all (a file not written by the gate) is refused
        bl.write_text("5\tA.lean\n", encoding="utf-8")
        check("RED (e): a baseline with NO header was not written by the gated refresh",
              any("no `# TOTAL" in x for x in audit_baseline_integrity(bl)),
              f"findings={audit_baseline_integrity(bl)}")
        # CONTROL: regenerating through the gate makes it self-consistent again
        rc = refresh_baseline(bl, c15, n15, "regenerate after the hand-edit", True, quiet=True)
        check("CONTROL: a gate-written refresh restores integrity",
              rc == 0 and not audit_baseline_integrity(bl),
              f"rc={rc} findings={audit_baseline_integrity(bl)}")

        # floors: a blinded (empty) scan must FAIL rather than green
        rc = evaluate({}, 0, {}, True, "self-test-blinded", 0, quiet=True)
        check("a BLINDED scan trips the non-vacuity floors", rc == 1, f"rc={rc}")

        print("")
        print("guard-discipline self-test: " + ("PASS" if ok else "FAIL"))
        return 0 if ok else 1
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="per-module `#guard` downward ratchet (see metatheory/docs/GUARD-DISCIPLINE.md)")
    ap.add_argument("--rev", help="scan a clean `git archive` extract of this revision (churn-safe)")
    ap.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    ap.add_argument("--update-baseline", action="store_true",
                    help="rewrite the baseline from the current census (retire converted rows). "
                         "REFUSES to raise any row or the total; requires --reason")
    ap.add_argument("--reason", help="why this refresh happens — stamped into the baseline header "
                                     "with the sha. Required by --update-baseline")
    ap.add_argument("--allow-increase", action="store_true",
                    help="⚑ permit a refresh that RAISES a row or the total. Still requires "
                         "--reason, and stamps INCREASED into the header")
    ap.add_argument("--only", action="append", metavar="PATH",
                    help="⚑ retire ONLY these rows (repeatable, paths relative to metatheory/). "
                         "Every other row keeps its standing value — so a lane in a shared tree "
                         "cannot absorb a sibling's in-flight guards. Use this by default")
    ap.add_argument("--top", type=int, default=0, help="also print the N heaviest modules")
    ap.add_argument("--self-test", action="store_true", help="red-proof against a synthetic tree")
    ap.add_argument("--metatheory-dir", type=Path, help="override the metatheory dir (testing)")
    args = ap.parse_args()

    if args.self_test:
        return run_self_test()

    root = repo_root()
    tmpdir = None
    try:
        if args.metatheory_dir:
            mt, label = args.metatheory_dir, str(args.metatheory_dir)
        elif args.rev:
            tmpdir = Path(tempfile.mkdtemp(prefix="guard-discipline-rev-"))
            mt, label = extract_metatheory(root, args.rev, tmpdir), args.rev
        else:
            mt, label = root / "metatheory", "working tree"
        if not mt.is_dir():
            print(f"check-guard-discipline: FATAL — no metatheory dir at {mt}", file=sys.stderr)
            return 2

        counts, n_files = scan(mt)

        if args.update_baseline:
            return refresh_baseline(args.baseline, counts, n_files,
                                    args.reason, args.allow_increase, only=args.only)

        rc = evaluate(counts, n_files, read_baseline(args.baseline),
                      enforce_floors=True, label=label, top=args.top)
        # ⚑ arm (e) — the LEDGER's own integrity. Reported after the census so a hand-edit
        # cannot be mistaken for a census finding, and it reds independently.
        integrity = audit_baseline_integrity(args.baseline)
        if integrity:
            print("")
            print("⚑ RED — the BASELINE ITSELF does not add up (a refresh was bypassed):")
            for f in integrity:
                print(f"   {f}")
            print("")
            print("FAIL: baseline integrity")
            rc = 1
        return rc
    except Exception as e:  # noqa: BLE001
        print(f"check-guard-discipline: FATAL — {e}", file=sys.stderr)
        return 2
    finally:
        if tmpdir:
            shutil.rmtree(tmpdir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
