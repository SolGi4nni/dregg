#!/usr/bin/env python3
"""check-ignored-test-routing.py — THE FOURTH DARKNESS: a test that compiles, is
wired, is in scope on every push, and still never executes, because it is `#[ignore]`d
and NOTHING passes `--ignored` at it.

═══ WHY THIS EXISTS, AND WHY IT IS NOT `armed-teeth.yml` ══════════════════════════
`scripts/check-never-run-targets.py` names this class in its own "what this cannot
see" section and hands it off:

    * A `#[ignore]`d test inside an otherwise-runnable target. That is
      `armed-teeth.yml`'s subject, and it is visible — libtest prints `ignored` —
      which this class is not.

The handoff was correct and the receiver leaked. `armed-teeth.yml`'s `binding-teeth`
job builds its `--test` list by GLOBBING FILENAMES:

    for f in circuit-prove/tests/*tooth*.rs circuit-prove/tests/*teeth*.rs

so an `#[ignore]`d test earns a nightly run by being in a file whose NAME contains
"tooth" or "teeth". That is not a property of the test. Measured 2026-08-07 at HEAD,
`circuit-prove/tests/` carries 103 `#[ignore]` attributes: 21 in the 14 glob-matched
files, 13 GPU (correctly owned by `[profile.gpu]`), and **69 reached by nothing at
all** — including `custom_binding_production_path`'s two forged-rejection poles,
`fold_unfoolability_forge`, `accumulator`'s `online_mixed_root_forgery_rejected`,
`membership_binding_mechanism`'s forged pole, and `recursion_vk_determinism`. Add
`circuit-prove/src/`'s own ignored lib tests and `lightclient/src/lib.rs`'s 15, which
a `--test <binary>` list cannot name even in principle, and the leak is structural.

⚑ THE GLOB IS THE WOUND, SO THE FIX MUST NOT BE ANOTHER DERIVATION FROM NAMES.
`armed-teeth.yml`'s own header already worked out the general shape and then applied it
one level too high:

    "AND A DERIVED LIST STILL NEEDS A FLOOR. Deriving instead of transcribing stops the
     list going STALE; it does not stop it going EMPTY or SHRINKING."

Right — and the converse is what this file is. A TRANSCRIBED roster cannot go empty by
a rename, and a COMPLETENESS GATE over it cannot go stale, because the gate's ground
truth is the tree's own `#[ignore]` attributes, re-read on every run. Neither half is
sufficient alone; the pair is.

═══ WHAT A "ROUTE" IS ═════════════════════════════════════════════════════════════
A route is a claim about WHERE a given `#[ignore]`d test executes, or an explicit,
reasoned statement that nothing does.

⚠ ONLY THREE ROUTES NAME SOMETHING THAT ACTUALLY RUNS THE TEST: `armed-nightly`,
`armed-dark` and `other-lane`. `gpu` names a profile that runs it ON A BOX WITH AN
ADAPTER, which no scheduled lane in this repository is. And `measurement`, `oversized`,
`exclusive` and `fixture-mint` are DELIBERATELY-NOT-ARMED: each records WHY a nightly
cannot serve that test, and each is still a test nothing runs. Saying so in four
specific words instead of one vague one is worth doing — but it is not a resolution,
and this header will not pretend otherwise. Those 13 + the 20 GPU + the 152 `unrouted`
are the standing residual, and the ratchet is what stops it growing.

⚑ AND ONE OF THEM IS A REAL PIN WELDED TO A WRITER.
`apex_shrink_gnark_fixture::derive_deployed_apex_vk_identity_and_check_fixture` is
rostered `fixture-mint` because it "(re)writes chain/gnark/fixtures/apex_vk_identity.json"
— but its own reason also says it "asserts the gnark fixture matches" the VK identity
derived from a fresh fold at HEAD. That is the deployed apex VK pin, and it runs nowhere,
because the assertion and the write live in ONE test and the write is what disqualifies
it from a nightly. Splitting them would let the pin be armed. Reported here rather than
repaired in an arming pass.


  armed-nightly  `.github/workflows/armed-teeth.yml`'s `binding-teeth` job, 05:00 UTC.
  armed-dark     `.github/workflows/armed-teeth.yml`'s `dark-binding-teeth` job — the 71
                 teeth this census found reached by NOTHING at HEAD. It is a separate job
                 with its own timeout on purpose: its aggregate wall clock on a hosted
                 runner has never been measured (the same footing `feature-gated-prove-teeth`
                 landed on, and its header says so), so it must not be able to time out the
                 lane that already works.
  gpu            `[profile.gpu]` in `.config/nextest.toml`, on a box with an adapter.
                 These fail CLOSED on a missing adapter BY DESIGN; a GPU-less nightly
                 must not run them.
  measurement    NOT ARMED — and not a tooth either. A perf/anatomy probe with no adversarial claim (in one
                 case — `dfa_routing_emit_gate::perf_prove_verify_breakdown` — the
                 `#[ignore]` reason says "PERF PROBE with NO assertion" outright).
                 Arming these buys nothing and costs the nightly's wall clock.
  oversized      NOT ARMED. The tree records a peak footprint LARGER THAN THE RUNNER. `ubuntu-latest`
                 is 4 vCPU / 16 GB; `mina_accumulator_fold`'s three tests record
                 117.8–118.3 GiB peak and `leaf_wrap_mint_blowup_repricing`'s records
                 "~118 GiB peak footprint (> RAM)". Scheduling these on a hosted runner
                 does not arm them, it manufactures an OOM that reads as a failing tooth.
  exclusive      NOT ARMED. The test's own `#[ignore]` reason says it must run ALONE (it measures a
                 process-wide resource). `[profile.armed]` sets `test-threads = 4`, so
                 running it there INVALIDATES it while looking like coverage.
  fixture-mint   NOT ARMED. Its effect is to WRITE a fixture into the tree. A nightly that mints
                 fixtures is a nightly that edits the repository.
  other-lane     Executed by a named non-`armed` lane (a different workflow/profile).
  unrouted       NOTHING RUNS IT. This is the honest bucket and it is a RATCHET: the
                 count may fall and must never rise.

═══ THE VERDICT ═══════════════════════════════════════════════════════════════════
FAILS on four things, and the second is the one no other check in this tree can see:

  1. AN UNROSTERED IGNORED TEST. A new `#[ignore]` with no row is dark by default and
     the gate says so on the day it lands, not six weeks later.
  2. A ROSTER ROW WHOSE TEST NO LONGER EXISTS. This is the silent-rot direction, and
     `.config/nextest.toml` documents that nextest itself is BLIND to it: measured
     2026-07-27 against three nextest versions, `test(~no_such_name)` is "SILENT.
     exit 0. Not a warning. Nothing is printed at all", and 21 of 41 such names in
     that file resolved to nothing. A roster that can name the dead is a roster that
     will, and a lane pointed at a dead name runs zero tests and reports green.
  3. THE `armed-nightly` COUNT FALLING BELOW ITS FLOOR — the same ratchet
     `armed-teeth.yml` applies to its own derived list, for the same reason.
  4. THE `unrouted` COUNT RISING ABOVE ITS CEILING.

⚠ WHAT THIS CANNOT SEE, STATED RATHER THAN HIDDEN:
  * It reads the SOURCE, not `cargo nextest list`, so it runs on any box in a second
    with no compile. The cost is that it cannot resolve `#[cfg]`-gated modules, macro-
    generated tests, or `required-features`. Those are the OTHER THREE sweeps' subject
    (`check-dark-targets.py`, `check-dark-modules.py`, `check-never-run-targets.py`).
    Pass `--from-nextest <file>` with the output of
    `cargo nextest list --workspace --run-ignored ignored-only` to cross-check the
    source scan against cargo's own resolve.
  * A route is a CLAIM that a lane runs the test. This gate checks that the claim is
    written down and that its subject exists. It does NOT verify the lane ran, and it
    cannot: that is `nightly-verdict`'s job in `armed-teeth.yml`.
  * ⚑ IT SAYS NOTHING ABOUT WHETHER AN ARMED TEST BITES. `armed-teeth.yml`'s own
    measurement is the standing reminder: when the glob-covered teeth were first armed,
    11 of 17 failed. Routing a test is a precondition for it biting, never evidence.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ROSTER = REPO / ".github" / "ignored-test-routes.txt"

ROUTES = {
    "armed-nightly",
    "armed-dark",
    "gpu",
    "measurement",
    "oversized",
    "exclusive",
    "fixture-mint",
    "other-lane",
    "unrouted",
}

# Ratchets. RAISE the floor when the armed set grows; LOWER the ceiling when an
# unrouted test gains a route. Never the other way round to make a red go green —
# that is the move this entire family of sweeps exists to make impossible.
FLOOR_ARMED = 21
FLOOR_ARMED_DARK = 71
CEILING_UNROUTED = 152

IGNORE_ATTR = re.compile(r"^\s*#\[(?:ignore\b|cfg_attr\([^)]*\bignore\b)")
FN_DECL = re.compile(r"\bfn\s+([A-Za-z0-9_]+)")


def tracked_rs_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "*.rs"], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout.splitlines()
    keep = []
    for rel in out:
        if "/target/" in rel or rel.startswith("vendor/"):
            continue
        keep.append(Path(rel))
    return keep


def package_of(rel: Path) -> str:
    """Nearest ancestor Cargo.toml's `name`. Cheap, and independent of any filename."""
    d = (REPO / rel).parent
    while True:
        manifest = d / "Cargo.toml"
        if manifest.is_file():
            m = re.search(r'(?m)^\s*name\s*=\s*"([^"]+)"', manifest.read_text())
            if m:
                return m.group(1)
        if d == REPO:
            return "?"
        d = d.parent


def scan_source() -> dict[tuple[str, str], Path]:
    """(package, test fn) -> file, for every `#[ignore]`d test in the tree."""
    found: dict[tuple[str, str], Path] = {}
    for rel in tracked_rs_files():
        try:
            lines = (REPO / rel).read_text(errors="replace").splitlines()
        except OSError:
            continue
        if not any(IGNORE_ATTR.match(line) for line in lines):
            continue
        pkg = package_of(rel)
        for i, line in enumerate(lines):
            if not IGNORE_ATTR.match(line):
                continue
            # The attribute may span lines (long `#[ignore = "..."]` reasons do).
            j, attr = i, line.strip()
            while j + 1 < len(lines) and (
                attr.count("[") > attr.count("]") or not attr.rstrip().endswith("]")
            ):
                j += 1
                attr += " " + lines[j].strip()
            for k in range(j + 1, min(j + 8, len(lines))):
                m = FN_DECL.search(lines[k])
                if m:
                    found[(pkg, m.group(1))] = rel
                    break
    return found


def load_roster() -> tuple[dict[tuple[str, str], str], list[str]]:
    rows: dict[tuple[str, str], str] = {}
    problems: list[str] = []
    if not ROSTER.is_file():
        problems.append(f"roster missing: {ROSTER}")
        return rows, problems
    for lineno, raw in enumerate(ROSTER.read_text().splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) < 3:
            problems.append(f"{ROSTER}:{lineno}: expected `<route> <package> <test_fn>`")
            continue
        route, pkg, fn = parts[0], parts[1], parts[2]
        if route not in ROUTES:
            problems.append(f"{ROSTER}:{lineno}: unknown route {route!r}")
            continue
        rows[(pkg, fn)] = route
    return rows, problems


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--from-nextest",
        metavar="FILE",
        help="output of `cargo nextest list --workspace --run-ignored ignored-only`, "
        "cross-checked against the source scan (see the header's blind spots)",
    )
    ap.add_argument(
        "--emit-armed-filter",
        metavar="ROUTE",
        nargs="?",
        const="armed-nightly",
        help="print a nextest filterset selecting exactly the tests on ROUTE "
        "(default armed-nightly), for `armed-teeth.yml` to consume instead of a "
        "filename glob. This is what makes the workflow's list a property of the "
        "TEST rather than of the file it happens to live in — and, because a "
        "filterset reaches lib tests, it can name the 28 `#[ignore]`d teeth in "
        "`circuit-prove/src/` that a `--test <binary>` list cannot express at all.",
    )
    ap.add_argument(
        "--emit-cargo-targets",
        metavar="ROUTE",
        nargs="?",
        const="armed-nightly",
        help="print the `cargo test` target selectors (`--lib` / `--test <binary>`) that "
        "cover ROUTE, derived from where each rostered test ACTUALLY LIVES. This is not a "
        "filename glob: the roster selects tests by NAME, and this only translates that "
        "selection into the target flags cargo needs. It emits `--lib` when the route holds "
        "any lib test — the 28 in `circuit-prove/src/` that no `--test <binary>` list can "
        "reach — which is the half `armed-teeth.yml`'s glob could never have expressed.",
    )
    args = ap.parse_args()

    found = scan_source()
    roster, problems = load_roster()

    if args.emit_armed_filter:
        route = args.emit_armed_filter
        if route not in ROUTES:
            print(f"unknown route {route!r}", file=sys.stderr)
            return 2
        names = sorted(fn for (_p, fn), r in roster.items() if r == route)
        if not names:
            # An empty filterset selects EVERYTHING under `--run-ignored ignored-only`,
            # which is the opposite of what the caller asked for. Refuse instead.
            print(f"::error::route {route!r} is empty — refusing to emit a filterset "
                  f"that would select the whole package", file=sys.stderr)
            return 2
        print(" or ".join(f"test(={n})" for n in names))
        return 0

    if args.emit_cargo_targets:
        route = args.emit_cargo_targets
        if route not in ROUTES:
            print(f"unknown route {route!r}", file=sys.stderr)
            return 2
        want = {k for k, r in roster.items() if r == route}
        paths = [found[k] for k in want if k in found]
        if not paths:
            print(f"::error::route {route!r} covers no live test", file=sys.stderr)
            return 2
        pkgs = {k[0] for k in want}
        flags: list[str] = []
        lib = any("/src/" in str(p) for p in paths)
        if lib:
            flags.append("--lib")
        bins = sorted({p.stem for p in paths if "/tests/" in str(p)})
        for b in bins:
            flags += ["--test", b]
        # ⚠ TARGET GRANULARITY IS COARSER THAN ROUTE GRANULARITY, and silently running the
        # difference is how a nightly comes to mint fixtures or thrash a 118 GiB measurement.
        # `apex_shrink_gnark_fixture` is the live example: one of its three `#[ignore]`d tests
        # is an adversarial pole (`shrink_pinned_to_foreign_apex_vk_rejects`) and two WRITE
        # FIXTURES. Selecting the binary selects all three, so every ignored test that shares
        # a selected target and is NOT on this route is skipped BY NAME.
        selected_targets = set(paths)
        for key, path in sorted(found.items(), key=lambda kv: kv[0]):
            if key in want:
                continue
            # `--lib` selects the WHOLE lib target, not just the modules the route names —
            # so every `#[ignore]`d lib test of a selected package is in scope, including
            # `circuit-prove/src/gpu_backend.rs`'s seven, which assert a real adapter and are
            # a guaranteed red on a GPU-less runner. Skip them BY NAME rather than trusting
            # that they live somewhere `--test` would not have reached.
            in_scope = path in selected_targets or (
                lib and "/src/" in str(path) and key[0] in pkgs
            )
            if in_scope:
                flags += ["--skip", key[1]]
        print(" ".join(flags))
        return 0

    unrostered = sorted(k for k in found if k not in roster)
    # The silent-rot direction nextest itself cannot report.
    dead_rows = sorted(k for k in roster if k not in found)

    by_route: dict[str, int] = {}
    for key, route in roster.items():
        if key in found:
            by_route[route] = by_route.get(route, 0) + 1

    print(f"ignored-test routing — {len(found)} `#[ignore]`d test(s) in the tree")
    for route in sorted(ROUTES):
        print(f"  {route:<14} {by_route.get(route, 0)}")

    if args.from_nextest:
        listed = set()
        for line in Path(args.from_nextest).read_text().splitlines():
            line = line.strip()
            if not line or line.endswith(":"):
                continue
            listed.add(line.split()[-1].split("::")[-1])
        only_cargo = sorted(n for n in listed if not any(n == fn for _p, fn in found))
        if only_cargo:
            print(
                f"\n⚠ {len(only_cargo)} test(s) cargo lists as ignored that the source "
                f"scan missed (macro-generated or `#[cfg]`-shaped):"
            )
            for n in only_cargo:
                print(f"    {n}")

    failed = False
    if problems:
        failed = True
        print("\n::error::roster is malformed")
        for p in problems:
            print(f"    {p}")

    if unrostered:
        failed = True
        print(f"\n::error::{len(unrostered)} `#[ignore]`d test(s) carry NO ROUTE.")
        print("::error::An ignored test with no route is executed by nothing, which is")
        print("::error::indistinguishable from a test that always passes. Give each a row in")
        print(f"::error::{ROSTER.relative_to(REPO)} — `unrouted` is an allowed answer and is")
        print("::error::the honest one; inventing a lane that does not run it is not.")
        for pkg, fn in unrostered:
            print(f"    {pkg}::{fn}   ({found[(pkg, fn)]})")

    if dead_rows:
        failed = True
        print(f"\n::error::{len(dead_rows)} roster row(s) name a test that no longer exists.")
        print("::error::This is the direction nextest is SILENT about (see the header): a lane")
        print("::error::pointed at a dead name runs zero tests and reports success. Delete the")
        print("::error::row in the same commit that deletes or renames the test.")
        for pkg, fn in dead_rows:
            print(f"    {pkg}::{fn}")

    for route, floor in (("armed-nightly", FLOOR_ARMED), ("armed-dark", FLOOR_ARMED_DARK)):
        have = by_route.get(route, 0)
        if have < floor:
            failed = True
            print(f"\n::error::{route} holds {have} test(s), below the floor of {floor}.")
            print("::error::A lane that arms fewer teeth than it claims reports on tests that did")
            print("::error::not happen. Do not lower the floor to clear this.")

    unrouted = by_route.get("unrouted", 0)
    if unrouted > CEILING_UNROUTED:
        failed = True
        print(
            f"\n::error::unrouted holds {unrouted} test(s), above the ceiling of "
            f"{CEILING_UNROUTED}."
        )
        print("::error::This ratchet only goes down. Route the new test, or say in the commit")
        print("::error::why the tree is knowingly getting darker.")

    if failed:
        return 1
    print("\nOK — every `#[ignore]`d test carries a route, and every route names a live test.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
