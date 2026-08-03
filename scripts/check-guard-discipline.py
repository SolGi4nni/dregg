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

═══ USAGE ═════════════════════════════════════════════════════════════════════════
  python3 scripts/check-guard-discipline.py                 # working tree, ratcheted
  python3 scripts/check-guard-discipline.py --rev HEAD      # clean extract of HEAD (churn-safe)
  python3 scripts/check-guard-discipline.py --top 25        # + the worst offenders
  python3 scripts/check-guard-discipline.py --update-baseline
  python3 scripts/check-guard-discipline.py --self-test     # red-proof (synthetic tree)
Exit: 0 ratchet-green · 1 violation or stale row or vacuous scan · 2 environment error
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


def write_baseline(path: Path, counts: dict[str, int], total_files: int) -> None:
    total = sum(counts.values())
    lines = [
        "# guard-discipline-baseline.txt — per-module `#guard` counts. A BURNDOWN LEDGER.",
        "# The gate (scripts/check-guard-discipline.py) reds when a module goes ABOVE its row,",
        "# BELOW it (a stale row — retire the number when you convert), or carries guards with",
        "# no row at all. So this file may only ever SHRINK. Policy: metatheory/docs/GUARD-DISCIPLINE.md.",
        f"# TOTAL {total} guards across {len(counts)} modules ({total_files} .lean files scanned).",
        "# format: <count><TAB><path relative to metatheory/>",
        "",
    ]
    for p in sorted(counts):
        lines.append(f"{counts[p]}\t{p}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


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
        write_baseline(bl, c5, n5)
        rc = evaluate(c5, n5, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("--update-baseline retires the rows and re-greens", rc == 0, f"rc={rc}")

        # the ratchet is one-way: the retired (smaller) baseline now REJECTS a regrowth
        _mk(mt, "A.lean", "#guard 1 == 1\n#guard 2 == 2\n#guard 3 == 3\n")
        c6, n6 = scan(mt)
        rc = evaluate(c6, n6, read_baseline(bl), False, "self-test", 0, quiet=True)
        check("the ratchet is ONE-WAY: regrowth past the retired row fails", rc == 1, f"rc={rc}")

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
                    help="rewrite the baseline from the current census (retire converted rows)")
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
            write_baseline(args.baseline, counts, n_files)
            print(f"wrote {args.baseline} — {sum(counts.values())} guards across "
                  f"{len(counts)} modules")
            return 0

        return evaluate(counts, n_files, read_baseline(args.baseline),
                        enforce_floors=True, label=label, top=args.top)
    except Exception as e:  # noqa: BLE001
        print(f"check-guard-discipline: FATAL — {e}", file=sys.stderr)
        return 2
    finally:
        if tmpdir:
            shutil.rmtree(tmpdir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
