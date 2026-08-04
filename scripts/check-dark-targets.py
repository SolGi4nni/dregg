#!/usr/bin/env python3
"""check-dark-targets.py — the compile-fail ratchet, as a script that can run anywhere.

═══ THE FIRST DARKNESS ══════════════════════════════════════════════════════════════
This is the first of the three sweeps over `.github/dark-targets.txt`, and until now it
was the only one with no script behind it:

  1. THIS                            catches a target that FAILS TO COMPILE
  2. `scripts/check-dark-modules.py` catches a file rustc NEVER OPENS
  3. `scripts/check-never-run-targets.py` catches a target nothing can EXECUTE

All three leave every `#[test]` in the target unable to fire, which is indistinguishable
from a falsifier that always passes. Sweeps 2 and 3 were `scripts/check-*.py` from birth,
so they have rows in `scripts/local-gates.sh` and run on any box. Sweep 1 lived as INLINE
SHELL inside one step of one job of `.github/workflows/ci.yml`, so the only machine that
could ever run it was a GitHub runner reaching step 7 of `clippy-correctness`.

═══ WHY THIS FILE EXISTS — TWO MEASURED HOLES ═══════════════════════════════════════

── HOLE 1: A GATE BEHIND A RED GATE IS NOT A GATE ───────────────────────────────────
The ratchet was step 7 of `clippy-correctness`. Step 6 is the correctness sweep, which
`exit 1`s when any `clippy::correctness` lint fires. GitHub Actions stops a job at the
first failed step, so a correctness hit anywhere in the workspace SKIPS steps 7, 8 and 9
— all three darkness sweeps — and the job's red says "correctness", never "dark".

MEASURED over every `ci.yml` run from 2026-08-01 to 2026-08-03 (34 runs, `gh run view
--json jobs`): the dark-target ratchet EXECUTED 3 TIMES AND WAS SKIPPED 31. A 91% skip
rate, and the skips are not random — they persist for as long as one correctness lint
stands. Two did: `dreggnet-game-board/tests/multi_round_fold.rs:533` and
`dregg-automatafl/src/legc_witness.rs:768`, both `this operation will always return zero`.

WHAT IT COST, exactly. `522b9c763` (2026-08-03 11:55) widened `ZkOracleAttestation::
content_commit` from one felt to `[CommitLane; 8]` in `deos-hermes` and `attested-dm`
and MISSED the same code in `commons-arbiter` and `confined-swarm`. Both crates' libs
stopped compiling — every `#[test]` in them unable to fire — and neither is on the
allowlist. Five CI runs covered that window (12:06, 13:22, 15:09, 15:13, 15:56) and in
ALL FIVE the ratchet step reads `skipped`. It was repaired at `f71f7f35e` (23:04) by a
human reading a build error, ~11h later, with no gate ever having said the word "dark".

The wasm job in that same workflow already carries this lesson in its own comment — "A
GATE BEHIND A RED GATE IS NOT A GATE" — for the identical reason, one job over. The
workflow fix is `if: ${{ !cancelled() }}` on the three sweep steps. The fix HERE is that
the ratchet is no longer reachable only through that one door.

── HOLE 2: THE RATCHET'S EVIDENCE IS A LOWER BOUND, AND IT DID NOT KNOW ──────────────
`dark-targets.txt`'s header has warned since 2026-07-25 that "a dark-target count taken
while ANY lib is red is a LOWER BOUND", and told a HUMAN to "fix libs first, sweep again,
and do not believe the first number." The gate encoded none of that. It compared cargo's
DIAGNOSTICS against the allowlist — and a target cargo never attempts emits no diagnostic
at all, so it cannot appear on either side of the comparison.

MEASURED on a three-crate synthetic workspace (`--self-test` reproduces it): with
`probe-dep` depending on `probe-base`, breaking `probe-base`'s lib under
`cargo check --workspace --all-targets --keep-going` yields

    error: could not compile `probe-base` (lib) due to 1 previous error
    error: could not compile `probe-base` (lib test) due to 1 previous error

and NOT ONE WORD about `probe-dep` — not its lib, not its integration test. `--keep-going`
does reach INDEPENDENT crates (breaking `probe-free` too names it), so the pruning is
exactly the dependency cone and nothing else.

The dangerous shape follows immediately: allowlist `probe-base (lib)` and the old ratchet
prints `2 known, 0 new, 0 stale` and PASSES, while every test in the cone below it is
unable to fire. One allowlist row would have bought silence over an arbitrarily large
population. That is the `minted-fail-open-gate-class` shape — a gate that reports and
proceeds — and closing it is why this script asks CARGO'S OWN RESOLVE for the dependency
graph rather than trusting the diagnostics to be complete.

So: a row whose kind PRUNES (`lib`, `proc-macro`, `custom-build`) makes every workspace
member in its reverse-dependency cone UNMEASURED, this gate says so by name, and it
REFUSES to render a `stale` verdict over an incomplete measurement. There is deliberately
no allowlist escape for that state — an escape for it IS the hole. Repair the lib.

═══ WHAT THIS STILL CANNOT SEE (stated, not hidden) ═════════════════════════════════
The unmeasured set is DERIVED from the dependency graph, not observed. It therefore
covers the one cause of non-attempt this repo has actually been bitten by (a red
dependency) and NOT a hypothetical cargo that silently declines a unit for some other
reason. Observing attempts directly needs `--message-format=json`'s `compiler-artifact`
stream, which would mean rewriting the correctness reader in step 6 that currently works
and has its own scar history (the `CARGO_TERM_COLOR` bug). That is a real residual and it
is not closed here.

Note also that `Checking`/`Compiling` lines are NOT a usable attempt oracle: cargo prints
nothing for a unit it finds fresh, so on any warm cache (every CI run — `Swatinem/
rust-cache`) most of the workspace is silent while perfectly measured.

═══ USAGE ═══════════════════════════════════════════════════════════════════════════
    python3 scripts/check-dark-targets.py --log clippy-correctness.log   # CI: read the sweep
    python3 scripts/check-dark-targets.py --sweep                        # local: run it too
    python3 scripts/check-dark-targets.py --sweep -p commons-arbiter     # narrow (no stale verdict)
    python3 scripts/check-dark-targets.py --print-dark                   # rows, no verdict
    python3 scripts/check-dark-targets.py --self-test                    # RED-PROOF, ~15s

═══ EXIT STATUS ═════════════════════════════════════════════════════════════════════
    0  no unlisted dark target, no stale row, measurement complete, scan non-vacuous
    1  a violation: a new dark target, a stale row, or a pruned (unmeasured) cone
    2  the scan could not run or could not be trusted (no log, no cargo activity in it,
       parser drift, missing allowlist, a workspace resolve that came back too small)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_LIST = REPO / ".github" / "dark-targets.txt"

# The sweep CI runs. `--keep-going` is NOT optional and never has been: without it cargo
# stops scheduling new units at the first failure and the log ends there, so the run
# reports ONE broken crate out of ~225 and the next push shows the next one.
DEFAULT_SWEEP = [
    "cargo", "clippy", "--workspace", "--all-targets", "--keep-going",
    "--message-format=short",
]

# ⚠ ANSI, STRIPPED UNCONDITIONALLY. This gate's predecessor could not fire for its whole
# life because `CARGO_TERM_COLOR: always` (a workflow-level env) is honoured by cargo even
# when its output is REDIRECTED TO A FILE, so every `error` in the log carried SGR escapes
# and the reader was anchored on the bare word. CI now sets `never`, but a reader that
# cannot be broken by a colour setting is strictly better than one that must be configured
# correctly at a distance.
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")

# `error: could not compile `pkg` (kind ["name"]) due to N previous errors`
# The trailing count moves on its own and is noise; the row is `pkg (kind ["name"])`.
ROW = re.compile(r"^error: could not compile `([^`]+)` \((.*)\) due to")
# The LOOSE detector, for parser drift. Any line that says a package could not compile and
# that ROW cannot parse means cargo's phrasing moved and this gate is now under-reporting —
# which is the exact way its predecessor went silent. Under-reporting must be LOUD.
LOOSE = re.compile(r"could not compile")

# Evidence that cargo actually ran. A log that contains none of this is not "clean", it is
# a log of nothing, and reporting `0 new, 0 stale` over it is the disease.
ACTIVITY = re.compile(
    r"^\s*(Checking|Compiling|Fresh|Finished|Building|Blocking)\b"
    r"|\.rs:\d+:\d+:"
    r"|^(error|warning)\b",
    re.M,
)

# A target kind that, when it fails, PRUNES: cargo cannot attempt anything that depends on
# it. `lib test` is NOT here — that unit is the lib source rebuilt with `--test`, and its
# failure does not stop the rlib from being produced for dependents.
PRUNING_KINDS = ("lib", "proc-macro", "custom-build")


def strip_ansi(text: str) -> str:
    return ANSI.sub("", text)


def parse_dark(log_text: str) -> tuple[set[str], list[str]]:
    """(rows, unparsed) — rows as `pkg (kind ["name"])`, plus any `could not compile`
    line ROW failed to parse (parser drift; the caller must refuse on a non-empty list)."""
    rows: set[str] = set()
    unparsed: list[str] = []
    for raw in strip_ansi(log_text).splitlines():
        line = raw.rstrip()
        m = ROW.match(line)
        if m:
            rows.add(f"{m.group(1)} ({m.group(2)})")
        elif LOOSE.search(line):
            unparsed.append(line)
    return rows, unparsed


def row_pkg_kind(row: str) -> tuple[str, str]:
    """`dregg-cell (lib)` -> (`dregg-cell`, `lib`); `p (test "x")` -> (`p`, `test`)."""
    m = re.match(r"^(.*) \((.*)\)$", row)
    if not m:
        return row, ""
    return m.group(1), m.group(2).split(" ", 1)[0].split('"', 1)[0].strip()


def known_rows(list_path: Path) -> set[str]:
    """The compile-fail rows. `file ` and `never-run ` rows belong to the other two
    sweeps; the three readers partition one list (one doctrine, one file)."""
    rows = set()
    for line in list_path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if s.startswith("file ") or s.startswith("never-run "):
            continue
        body = s.split("#", 1)[0].strip()
        if body:
            rows.add(body)
    return rows


def cargo_metadata(repo: Path) -> dict:
    out = subprocess.run(
        ["cargo", "metadata", "--format-version", "1"],
        cwd=repo, capture_output=True, text=True,
    )
    if out.returncode != 0:
        print(f"::error::check-dark-targets: cargo metadata failed — the workspace does "
              f"not resolve, so the pruned-cone check cannot run and this gate refuses to "
              f"render a verdict it cannot support.\n{out.stderr[-2000:]}", file=sys.stderr)
        sys.exit(2)
    return json.loads(out.stdout)


def reverse_cone(meta: dict, seed_pkgs: set[str]) -> set[str]:
    """Workspace members that transitively depend on any package in `seed_pkgs`, seeds
    included. Edges come from `resolve` — CARGO'S OWN RESOLVE, the same oracle
    `check-never-run-targets.py` uses, so an optional dependency that is not activated
    does not manufacture a phantom cone. All dep kinds count: a DEV-dependency on a red
    lib prunes the dependent's test targets, which is precisely the population at stake.
    """
    id_to_name = {p["id"]: p["name"] for p in meta["packages"]}
    members = {id_to_name[i] for i in meta.get("workspace_members", []) if i in id_to_name}

    rev: dict[str, set[str]] = {}
    for node in (meta.get("resolve") or {}).get("nodes", []) or []:
        dependent = id_to_name.get(node["id"])
        if dependent is None:
            continue
        for dep in node.get("deps", []):
            dep_name = id_to_name.get(dep.get("pkg", ""))
            if dep_name is not None:
                rev.setdefault(dep_name, set()).add(dependent)

    seen: set[str] = set()
    stack = list(seed_pkgs)
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(rev.get(cur, ()))
    return seen & members


# ═════════════════════════════════════════════════════════════════════════════════════
# THE REACHABILITY GUARD — because hole 1 was a WORKFLOW-STRUCTURE bug
# ═════════════════════════════════════════════════════════════════════════════════════
# Fixing the three `if:` conditions in ci.yml fixes today. It does not stop the next step
# from being appended without one, which puts every sweep after it back behind a red gate
# — and nothing in this repo checks workflow structure at all. So the gate guards its own
# reachability: every sweep step in `clippy-correctness` must carry an `if:`, or this
# fails. Text-scanned rather than YAML-parsed on purpose — no repo check script imports
# PyYAML, and a gate that dies on a missing module is a gate that gets deleted.
JOB_HEADER = re.compile(r"^  ([A-Za-z0-9_-]+):\s*$")
STEP_START = re.compile(r"^      - ")
GUARDED_JOB = "clippy-correctness"


def sweep_steps_missing_guard(workflow: Path) -> tuple[list[str], int]:
    """(names of unguarded sweep steps, number of sweep steps seen).

    A "sweep step" is one whose `run:` invokes a `scripts/check-…` reader — the darkness
    sweeps. The correctness sweep itself is deliberately NOT one: it is the step whose
    failure must not silence the others, and it has no `if:`.
    """
    lines = workflow.read_text(encoding="utf-8").splitlines()
    in_job = False
    blocks: list[list[str]] = []
    for line in lines:
        m = JOB_HEADER.match(line)
        if m:
            in_job = m.group(1) == GUARDED_JOB
            continue
        if not in_job:
            continue
        if STEP_START.match(line):
            blocks.append([line])
        elif blocks:
            blocks[-1].append(line)

    unguarded, seen = [], 0
    for block in blocks:
        # ⚑ COMMENTS BELONG TO THE NEXT STEP, NOT THIS ONE. A block runs until the next
        # `      - `, so a comment written ABOVE the following step lands here. The first
        # draft of this scan tested the raw text and reported the correctness sweep as an
        # unguarded sweep step, purely because the ratchet's comment block below it names
        # `scripts/check-dark-targets.py`. Caught by R15 against the real ci.yml.
        code = [l for l in block if not l.lstrip().startswith("#")]
        if not any("scripts/check-" in l for l in code):
            continue
        seen += 1
        name = next((l.split("name:", 1)[1].strip()
                     for l in code if "name:" in l), code[0].strip())
        if not any(re.match(r"^\s+if:\s*\S", l) for l in code):
            unguarded.append(name)
    return unguarded, seen


def run_sweep(repo: Path, packages: list[str], sweep: list[str]) -> str:
    cmd = list(sweep)
    for p in packages:
        cmd += ["-p", p]
    if packages:
        cmd = [c for c in cmd if c != "--workspace"]
    env = dict(os.environ)
    # `never`, not a sed pipeline: this log is read by machines only. Belt AND braces —
    # `strip_ansi` already makes the reader colour-proof.
    env["CARGO_TERM_COLOR"] = "never"
    env["CARGO_PROFILE_DEV_DEBUG"] = "0"
    out = subprocess.run(cmd, cwd=repo, capture_output=True, text=True, env=env)
    return out.stdout + out.stderr


def verdict(
    log_text: str,
    list_path: Path,
    repo: Path,
    partial: bool,
    min_members: int,
) -> int:
    if not log_text.strip():
        print("::error::check-dark-targets: the sweep log is EMPTY. A ratchet that reads "
              "nothing reports `0 new, 0 stale` and looks exactly like coverage — that is "
              "how this gate's predecessor stayed silent for its whole life.",
              file=sys.stderr)
        return 2
    if not ACTIVITY.search(strip_ansi(log_text)):
        print("::error::check-dark-targets: the sweep log records NO CARGO ACTIVITY (no "
              "Checking/Compiling/Fresh/Finished line, no diagnostic). cargo did not run, "
              "or its output went somewhere else. Refusing to render a verdict.",
              file=sys.stderr)
        return 2
    if not list_path.is_file():
        print(f"::error::check-dark-targets: allowlist not found: {list_path}. A missing "
              f"file must never read as 'nothing is dark' — create it empty if the set is "
              f"genuinely empty.", file=sys.stderr)
        return 2

    dark_now, unparsed = parse_dark(log_text)
    if unparsed:
        print("::error::check-dark-targets: PARSER DRIFT — %d line(s) say a package could "
              "not compile and this gate could not parse them into rows. It is therefore "
              "UNDER-REPORTING darkness by an unknown amount, which is the precise way a "
              "ratchet goes quiet. Fix the parse; do not ignore these:" % len(unparsed),
              file=sys.stderr)
        for line in unparsed[:20]:
            print(f"    UNPARSED  {line}", file=sys.stderr)
        return 2

    meta = cargo_metadata(repo)
    id_to_name = {p["id"]: p["name"] for p in meta["packages"]}
    members = {id_to_name[i] for i in meta.get("workspace_members", []) if i in id_to_name}
    if len(members) < min_members:
        print(f"::error::check-dark-targets: the workspace resolve came back with only "
              f"{len(members)} member(s) (floor {min_members}). Under a truncated resolve "
              f"almost nothing can be attempted and almost nothing reads dark — the gate "
              f"would go green by scanning a workspace that is not there.", file=sys.stderr)
        return 2

    known = known_rows(list_path)
    new = sorted(dark_now - known)
    stale = sorted(known - dark_now)

    # ── the pruned cone: what this sweep COULD NOT HAVE MEASURED ──────────────────────
    # ⚑ THE PRUNING PACKAGE IS IN ITS OWN CONE, and leaving it out was a bug in the first
    # draft of this gate — caught by R6 of its own self-test. A package's integration
    # tests, bins, examples and benches all link its lib, so a red lib prunes them too:
    # break `probe-free`'s lib and cargo names `(lib)` and `(lib test)` and NEVER
    # `(test "t")`. So a dark LIB can never be fully allowlisted — the rows for the
    # targets it pruned do not exist to be written down. Repair it; that is the only exit.
    pruning_pkgs = {
        pkg for pkg, kind in (row_pkg_kind(r) for r in dark_now)
        if kind in PRUNING_KINDS
    }
    cone = reverse_cone(meta, pruning_pkgs) if pruning_pkgs else set()
    unmeasured_own = sorted(cone & pruning_pkgs)
    unmeasured_down = sorted(cone - pruning_pkgs)
    unmeasured = unmeasured_own + unmeasured_down

    print("check-dark-targets: %d workspace member(s); %d dark row(s) in the log; "
          "%d known row(s); %d new; %d unmeasured package(s) below a pruning failure%s."
          % (len(members), len(dark_now), len(known), len(new), len(unmeasured),
             "; PARTIAL sweep (staleness not judged)" if partial else ""))

    fail = False

    if new:
        fail = True
        print("::error::a target went DARK and is not on the known list. A test target that "
              "does not compile is a falsifier that cannot fire — it is not a warning.",
              file=sys.stderr)
        for r in new:
            print(f"  NEW DARK: {r}", file=sys.stderr)
        print("\nRepair it, or add the row to %s with a one-line reason and an owner.\n"
              "Reproduce locally with:\n"
              "  python3 scripts/check-dark-targets.py --sweep\n"
              "(which runs `%s` — `--keep-going` is REQUIRED: a plain --all-targets run\n"
              " ABORTS at the first broken target and shows you nothing past it.)"
              % (list_path, " ".join(DEFAULT_SWEEP)), file=sys.stderr)

    if unmeasured:
        fail = True
        print("\n::error::THE SWEEP IS A LOWER BOUND: %d workspace package(s) were NEVER "
              "ATTEMPTED, because a package they depend on failed to build. cargo emits no "
              "diagnostic whatsoever for a pruned unit, so every #[test] in these is unable "
              "to fire and NO ROW ANYWHERE records it — not here, not in the allowlist."
              % len(unmeasured), file=sys.stderr)
        print("  pruned by: " + ", ".join(sorted(pruning_pkgs)), file=sys.stderr)
        for p in unmeasured_own:
            print(f"    UNMEASURED (its OWN bins/tests/examples)  {p}", file=sys.stderr)
        for p in unmeasured_down[:40]:
            print(f"    UNMEASURED (downstream)  {p}", file=sys.stderr)
        if len(unmeasured_down) > 40:
            print(f"    … and {len(unmeasured_down) - 40} more downstream (listing capped)",
                  file=sys.stderr)
        print("\n  FIX: repair the pruning package(s) and sweep AGAIN — the second sweep is\n"
              "  the one whose number means anything. There is deliberately NO allowlist row\n"
              "  for this state: allowlisting a red lib buys silence over its whole cone, and\n"
              "  an escape hatch for that IS the hole this check exists to close.",
              file=sys.stderr)

    if stale and not partial and not unmeasured:
        fail = True
        print(f"\n::error::these rows in {list_path} now COMPILE. Delete them — a stale "
              f"allowlist is how the next dark target gets waved through.", file=sys.stderr)
        for r in stale:
            print(f"  NO LONGER DARK: {r}", file=sys.stderr)
    elif stale and unmeasured:
        print("\n::warning::%d allowlisted row(s) are absent from this log, but the sweep was "
              "PRUNED (see above), so absence is not evidence they compile. The staleness "
              "verdict is WITHHELD rather than guessed." % len(stale), file=sys.stderr)
    elif stale and partial:
        print("\n::warning::%d allowlisted row(s) are absent from this PARTIAL sweep. "
              "Staleness is only judged by a full-workspace run." % len(stale),
              file=sys.stderr)

    if fail:
        return 1
    print("dark-target ratchet: %d known, 0 new, 0 stale, 0 unmeasured." % len(known))
    return 0


def reachability_verdict(repo: Path) -> int:
    """The gate's own reachability in CI. Separate from `verdict` on purpose: `verdict`
    is about a log and an allowlist and is exercised against synthetic workspaces that
    have no workflows, while THIS is about the real repo's `ci.yml`."""
    workflow = repo / ".github" / "workflows" / "ci.yml"
    if not workflow.is_file():
        print(f"::error::check-dark-targets: {workflow} is missing, so this gate cannot "
              f"confirm it is REACHABLE in CI. Refusing to report green — an unreachable "
              f"gate is exactly what hid commons-arbiter and confined-swarm.",
              file=sys.stderr)
        return 2
    unguarded, seen = sweep_steps_missing_guard(workflow)
    if seen == 0:
        print(f"::error::check-dark-targets: found NO sweep steps in the `{GUARDED_JOB}` "
              f"job of {workflow}. Either the job was renamed or the sweeps were removed "
              f"— and a reachability check that inspects nothing passes trivially, which "
              f"is the disease it exists to catch.", file=sys.stderr)
        return 1
    if unguarded:
        print("::error::%d darkness sweep step(s) in `%s` carry NO `if:` condition, so a "
              "failure in ANY earlier step SKIPS them. Actions stops a job at the first "
              "failed step; that is how this ratchet was skipped on 31 of 34 runs while "
              "two crates sat dark. Add `if: ${{ !cancelled() }}`:"
              % (len(unguarded), GUARDED_JOB), file=sys.stderr)
        for n in unguarded:
            print(f"    UNREACHABLE-ON-EARLIER-FAILURE  {n}", file=sys.stderr)
        return 1
    print("check-dark-targets: %d sweep step(s) in `%s` all carry an `if:` — reachable "
          "even when an earlier step fails." % (seen, GUARDED_JOB))
    return 0


# ═════════════════════════════════════════════════════════════════════════════════════
# THE RED PROOF
# ═════════════════════════════════════════════════════════════════════════════════════
# ⚑ A GATE NOBODY TRIED TO BREAK IS A SUSPICION, NOT A GATE. Every scenario below runs a
# REAL cargo over a REAL (tiny) workspace and asserts the exit code — including R4, which
# is the case the shipped ratchet PASSED and this one must refuse. `cargo check` rather
# than `cargo clippy` so the proof does not need the clippy component; the
# `could not compile` phrasing is identical for both, which R2 pins.

PROBE_CRATES = {
    "base": [],
    "dep": ["probe-base"],
    "free": [],
}


def _write_probe(root: Path, broken_libs: set[str], broken_tests: set[str]) -> None:
    (root / "Cargo.toml").write_text(
        '[workspace]\nresolver = "2"\nmembers = ["base", "dep", "free"]\n', encoding="utf-8"
    )
    for name, deps in PROBE_CRATES.items():
        d = root / name
        (d / "src").mkdir(parents=True, exist_ok=True)
        man = (
            f'[package]\nname = "probe-{name}"\nversion = "0.0.0"\nedition = "2021"\n'
            f'[lib]\npath = "src/lib.rs"\n'
        )
        if deps:
            man += "[dependencies]\n" + "".join(
                f'{x} = {{ path = "../{x[len("probe-"):]}" }}\n' for x in deps
            )
        (d / "Cargo.toml").write_text(man, encoding="utf-8")
        (d / "src" / "lib.rs").write_text(
            'pub fn ok() -> u32 { "THIS IS THE DELIBERATE BREAK" }\n'
            if name in broken_libs else "pub fn ok() -> u32 { 1 }\n", encoding="utf-8")
        tests = d / "tests"
        tests.mkdir(exist_ok=True)
        # A broken INTEGRATION TEST prunes nothing — it is a leaf. That is what makes it
        # the one shape a row in the allowlist can honestly cover.
        (tests / "t.rs").write_text(
            '#[test]\nfn guard() { let _: u32 = "THE DELIBERATE BREAK"; }\n'
            if name in broken_tests else
            f"#[test]\nfn guard() {{ assert_eq!(probe_{name}::ok(), 1); }}\n", encoding="utf-8")


def _probe_verdict(root: Path, allow: str, broken_libs: set[str],
                   broken_tests: set[str] = frozenset()) -> tuple[int, str]:
    _write_probe(root, broken_libs, broken_tests)
    listing = root / "allow.txt"
    listing.write_text(allow, encoding="utf-8")
    log = run_sweep(root, [], ["cargo", "check", "--workspace", "--all-targets",
                              "--keep-going", "--message-format=short"])
    import io
    from contextlib import redirect_stderr, redirect_stdout
    buf = io.StringIO()
    with redirect_stdout(buf), redirect_stderr(buf):
        code = verdict(log, listing, root, partial=False, min_members=1)
    return code, buf.getvalue()


def self_test() -> int:
    scenarios: list[tuple[str, str, set[str], set[str], int, str | None]] = [
        # (name, allowlist, broken libs, broken tests, expected exit, required substring)
        ("R1 green baseline: nothing dark, empty list -> PASS",
         "# empty\n", set(), set(), 0, "0 new, 0 stale"),
        ("R2 an INDEPENDENT lib goes dark, unlisted -> FAIL",
         "# empty\n", {"free"}, set(), 1, "NEW DARK: probe-free (lib)"),
        ("R3 a DEPENDED-ON lib goes dark -> FAIL, and the cone is NAMED",
         "# empty\n", {"base"}, set(), 1, "UNMEASURED (downstream)  probe-dep"),
        # ⚑ R4 IS THE HOLE THIS GATE EXISTS FOR. With `probe-base` allowlisted the shipped
        # ratchet computes `new = {}`, `stale = {}` and prints `0 new, 0 stale` — GREEN —
        # while probe-dep's lib and its integration test cannot be attempted at all, and
        # no row anywhere records them. This gate must refuse.
        ("R4 an ALLOWLISTED dark lib still prunes its cone -> FAIL (the shipped hole)",
         "probe-base (lib)  # deliberate\nprobe-base (lib test)  # deliberate\n",
         {"base"}, set(), 1, "THE SWEEP IS A LOWER BOUND"),
        ("R5 a row that compiles again is STALE -> FAIL",
         "probe-free (lib)  # deliberate\n", set(), set(), 1,
         "NO LONGER DARK: probe-free (lib)"),
        # A broken INTEGRATION TEST is a leaf: it prunes nothing, so the measurement is
        # complete and a row can honestly cover it. This is the gate's only green-with-
        # darkness shape, and R7 is its other side.
        ("R6 a dark LEAF target, correctly listed -> PASS",
         'probe-free (test "t")  # deliberate\n', set(), {"free"}, 0, "1 known, 0 new"),
        ("R7 the same dark LEAF target, unlisted -> FAIL",
         "# empty\n", set(), {"free"}, 1, 'NEW DARK: probe-free (test "t")'),
    ]

    ok = True
    with tempfile.TemporaryDirectory(prefix="dark-targets-selftest-") as td:
        root = Path(td)
        for name, allow, broken, broken_t, want, needle in scenarios:
            code, out = _probe_verdict(root, allow, broken, broken_t)
            good = code == want and (needle is None or needle in out)
            ok &= good
            print(f"  [{'ok ' if good else 'FAIL'}] {name}   (exit {code}, want {want})")
            if not good:
                if needle is not None and needle not in out:
                    print(f"         expected output to contain: {needle!r}")
                print("         --- output ---")
                for line in out.splitlines():
                    print(f"         {line}")

    # ── log-level refusals: no cargo needed, but they are the anti-vacuity legs ────────
    with tempfile.TemporaryDirectory(prefix="dark-targets-selftest-log-") as td:
        root = Path(td)
        _write_probe(root, set(), set())
        listing = root / "allow.txt"
        listing.write_text("# empty\n", encoding="utf-8")
        import io
        from contextlib import redirect_stderr, redirect_stdout

        def run(log: str) -> int:
            buf = io.StringIO()
            with redirect_stdout(buf), redirect_stderr(buf):
                return verdict(log, listing, root, partial=False, min_members=1)

        legs = [
            ("R8 an EMPTY log refuses (does not read as clean)", "", 2),
            ("R9 a log with no cargo activity refuses", "hello\nworld\n", 2),
            ("R10 PARSER DRIFT refuses (a `could not compile` line ROW cannot parse)",
             "    Checking probe-base v0.0.0\n"
             "error: could not compile `probe-base` -- phrasing moved\n", 2),
            # ⚑ R11 IS THE CARGO_TERM_COLOR CLASS. This exact log — SGR escapes around
            # `error` — made the shipped reader's `dark-now.txt` ALWAYS EMPTY.
            ("R11 an ANSI-COLOURED log still parses (the CARGO_TERM_COLOR class)",
             "    \x1b[1m\x1b[32mChecking\x1b[0m probe-base v0.0.0\n"
             "\x1b[1m\x1b[91merror\x1b[0m: could not compile `probe-free` (lib) due to 1 "
             "previous error\n", 1),
        ]
        for name, log, want in legs:
            code = run(log)
            good = code == want
            ok &= good
            print(f"  [{'ok ' if good else 'FAIL'}] {name}   (exit {code}, want {want})")

    # ── R12-R14: the REACHABILITY guard, red-proved against synthetic workflows ───────
    GUARDED = (
        "jobs:\n"
        "  clippy-correctness:\n"
        "    steps:\n"
        "      - name: correctness sweep over every target\n"
        "        run: cargo clippy --workspace\n"
        "      - name: dark-target ratchet\n"
        "        if: ${{ !cancelled() }}\n"
        "        run: python3 scripts/check-dark-targets.py --log x.log\n"
    )
    UNGUARDED = GUARDED.replace("        if: ${{ !cancelled() }}\n", "")
    # The same steps under a DIFFERENT job name: the scan must find nothing, which the
    # `seen == 0` leg turns into a failure rather than a trivial pass.
    OTHER_JOB = GUARDED.replace("  clippy-correctness:\n", "  something-else:\n")
    with tempfile.TemporaryDirectory(prefix="dark-targets-selftest-wf-") as td:
        wf = Path(td) / "ci.yml"
        for name, body, want_unguarded, want_seen in [
            ("R12 a guarded sweep step passes the reachability check", GUARDED, 0, 1),
            ("R13 an UNGUARDED sweep step is caught (hole 1, as a check)", UNGUARDED, 1, 1),
            ("R14 the job renamed away -> scan sees nothing (must not pass trivially)",
             OTHER_JOB, 0, 0),
        ]:
            wf.write_text(body, encoding="utf-8")
            unguarded, seen = sweep_steps_missing_guard(wf)
            good = len(unguarded) == want_unguarded and seen == want_seen
            ok &= good
            print(f"  [{'ok ' if good else 'FAIL'}] {name}   "
                  f"(unguarded={len(unguarded)} want {want_unguarded}, "
                  f"seen={seen} want {want_seen})")

    # ── R15: and the REAL ci.yml must be guarded right now ───────────────────────────
    real = REPO / ".github" / "workflows" / "ci.yml"
    if real.is_file():
        unguarded, seen = sweep_steps_missing_guard(real)
        good = not unguarded and seen >= 3
        ok &= good
        print(f"  [{'ok ' if good else 'FAIL'}] R15 the real ci.yml: {seen} sweep step(s), "
              f"{len(unguarded)} unguarded   (want >=3 seen, 0 unguarded)")
        for n in unguarded:
            print(f"         UNGUARDED: {n}")

    if ok:
        print("check-dark-targets --self-test: PASS — every leg red-proved, including the "
              "allowlisted-dark-lib cone (R4) the shipped ratchet passed.")
        return 0
    print("check-dark-targets --self-test: FAIL — a leg did not behave as specified above.",
          file=sys.stderr)
    return 1


def main() -> int:
    ap = argparse.ArgumentParser(
        description="the compile-fail ratchet over .github/dark-targets.txt",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--log", type=Path,
                    help="read an existing sweep log (CI passes clippy-correctness.log)")
    ap.add_argument("--sweep", action="store_true",
                    help="run the sweep here (default when --log is absent)")
    ap.add_argument("--list", type=Path, default=DEFAULT_LIST)
    ap.add_argument("--repo", type=Path, default=REPO)
    ap.add_argument("-p", "--package", action="append", default=[],
                    help="narrow the sweep to these packages (staleness is then not judged)")
    ap.add_argument("--print-dark", action="store_true",
                    help="print the parsed dark rows and exit 0, no verdict")
    ap.add_argument("--min-members", type=int, default=50,
                    help="anti-vacuity floor on the workspace resolve (default 50)")
    ap.add_argument("--self-test", action="store_true",
                    help="RED-PROOF: break real crates in a temp workspace, assert the exits")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    if shutil.which("cargo") is None:
        print("::error::check-dark-targets: cargo not on PATH — this gate cannot run, and a "
              "gate that cannot run must say so rather than exit 0.", file=sys.stderr)
        return 2

    if args.log is not None:
        if not args.log.is_file():
            print(f"::error::check-dark-targets: sweep log not found: {args.log}. The step "
                  f"that produces it did not run, so this gate has no evidence.",
                  file=sys.stderr)
            return 2
        log_text = args.log.read_text(encoding="utf-8", errors="replace")
    else:
        log_text = run_sweep(args.repo, args.package, DEFAULT_SWEEP)

    if args.print_dark:
        rows, unparsed = parse_dark(log_text)
        for r in sorted(rows):
            print(r)
        for line in unparsed:
            print(f"UNPARSED  {line}", file=sys.stderr)
        return 0

    # Both verdicts always run, and the worse one wins — the reachability check must not
    # sit behind the darkness check for the same reason the darkness check must not sit
    # behind the correctness sweep.
    dark = verdict(
        log_text, args.list, args.repo,
        partial=bool(args.package), min_members=args.min_members,
    )
    reach = reachability_verdict(args.repo)
    return max(dark, reach)


if __name__ == "__main__":
    sys.exit(main())
