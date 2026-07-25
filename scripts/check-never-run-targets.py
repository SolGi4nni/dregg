#!/usr/bin/env python3
"""check-never-run-targets.py — a test target that COMPILES, is REACHABLE, and still
never executes in CI.

═══ THE THIRD DARKNESS ════════════════════════════════════════════════════════════
This is the third sweep over `.github/dark-targets.txt`, and it exists because the
first two cannot see this failure at all:

  1. the `dark-target ratchet`      catches a target that FAILS TO COMPILE
  2. `scripts/check-dark-modules.py` catches a file rustc NEVER OPENS
  3. THIS                            catches a target that compiles, is wired, and
                                     that NO WORKFLOW CAN EVER EXECUTE

All three leave every `#[test]` in the target unable to fire. The first two are at
least loud somewhere — a diagnostic, or an absent name. This one is SILENT IN A NEW
WAY: cargo prints *nothing whatsoever* for a target whose `required-features` are
off. Not `ignored`, not `0 filtered out` — no line at all. A whole-file
`#![cfg(feature = "x")]` is worse still: the binary is built, runs, and reports
`test result: ok. 0 passed; 0 failed`, which reads exactly like a passing suite.

  A guard that cannot run is indistinguishable from a guard that always passes.

═══ WHY `required-features` IS NOT THE QUESTION ═══════════════════════════════════
⚠ READ THIS BEFORE TRUSTING ANY HAND COUNT. The obvious sweep — "grep the manifests
for `required-features` that no workflow names" — is WRONG IN BOTH DIRECTIONS, and
was measured wrong by 20 targets on 2026-07-25.

Cargo UNIFIES features across a `--workspace` resolve, including through
DEV-DEPENDENCIES. `dreggnet-market` dev-depends on `dreggnet-catalog` with
`features = ["private-fhegg-game-consequence"]`, that feature turns on
`dreggnet-market/private-attested-clearing`, which turns on `private-clearing` and
`fhegg-fhe/amm-input-binding`. So fifteen targets whose manifests say
`required-features = ["amm-input-binding"]` / `["private-clearing"]` — and which a
manifest-only reading calls dark — are ACTIVE on every `cargo test --workspace`.
Conversely a feature can be off despite appearing on a workflow command line, if
that command line is a `cargo run`/`cargo build` rather than a test invocation.

So the oracle here is CARGO'S OWN RESOLVE (`cargo metadata`), never the manifest.
The check is PER-INVOCATION — one single `cargo test` must both put the target in
scope AND activate its whole gate:

    gate(T)         = required-features(T) ∪ feature names in T's file-level `#![cfg]`
    scope(I)        = the targets invocation I selects (`--test N` narrows it to N;
                      `--lib`/`--bins` alone selects no integration test at all)
    activated(I, P) = cargo metadata's resolved features for P
                      ∪ the features I passes for P
    T in P RUNS  iff  ∃ invocation I:  T ∈ scope(I)  ∧  gate(T) ⊆ activated(I, P)

⚠ THE ∃ IS OVER ONE INVOCATION, NOT A UNION OF ALL OF THEM. Unioning says a target
is covered when invocation A has it in scope and a DIFFERENT invocation B turns its
feature on. That is precisely the shape of `dregg-lean-ffi`'s probes and it hid four
of them: `cargo test --workspace` has all six in scope and arms none, while
`scripts/check-lean-marshal.sh` arms `lean-lib` and names only two by `--test`.

═══ WHAT THIS CANNOT SEE (stated, not hidden) ═════════════════════════════════════
  * PLATFORM gates. A `#![cfg(target_os = "macos")]` target is dark on a Linux-only
    lane, and this sweep does not model per-job runner OS. That hole is real and has
    already cost once: `dregg-lean-ffi/tests/embeddable_runtime_probe.rs` is
    macOS-only and is armed only by `scripts/check-lean-marshal.sh`, which runs on
    `ubuntu-latest` — so it reported `ok. 0 passed` on every CI run while its Linux
    twin `embeddable_runtime_probe_linux.rs` was armed by nothing at all.
  * A test that RUNS and asserts nothing. That is the self-skipping-test class; a
    different sweep's job.
  * `cargo metadata` unions all platforms unless `--filter-platform` is given, so it
    OVER-approximates activation and therefore UNDER-reports darkness. That is the
    safe direction for a ratchet: it never invents a dark target.
  * `--no-default-features` is not modelled: an invocation that strips defaults is
    still credited with the resolve's default features. Over-approximates activation,
    same safe direction.
  * A `#[ignore]`d test inside an otherwise-runnable target. That is `armed-teeth.yml`'s
    subject, and it is visible — libtest prints `ignored` — which this class is not.

⚠ SO THE COUNT IS A LOWER BOUND, exactly like the compile-fail ratchet's is while any
lib is red. Every approximation above is deliberately biased toward calling a target
runnable, because a ratchet that invents dark targets gets disabled.

═══ THE RATCHET ═══════════════════════════════════════════════════════════════════
Two-sided, sharing `.github/dark-targets.txt` with the other two sweeps. Rows are
prefixed `never-run ` so all three readers partition one list:

    never-run <package> <kind> <name>   # why, who owns it, and what arms it instead

A never-run target NOT on the list fails. A row that became executable ALSO fails —
a stale allowlist is how the next one gets waved through.

Usage:  check-never-run-targets.py [--list PATH] [--print-dark] [--explain]
Exit:   0 clean · 1 ratchet violation · 2 usage/environment error
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_LIST = REPO / ".github" / "dark-targets.txt"

# A file-level `#![cfg(...)]`. Only the OUTER attribute matters: it empties the whole
# crate, which is what turns a test binary into `ok. 0 passed`.
INNER_CFG = re.compile(r"^\s*#!\[cfg\((.*?)\)\]", re.M | re.S)
FEATNAME = re.compile(r'feature\s*=\s*"([^"]+)"')

# A cargo invocation that RUNS tests. `cargo build`/`cargo run` with `--features x`
# does NOT arm x's test targets, and conflating the two is how `--features lean-lib`
# in lean-seed.yml looked like coverage it never provided.
CARGO_TEST = re.compile(
    r"\b(?:cargo\s+(?:\+\S+\s+)?(?:test|nextest\s+run)|wasm-pack\s+test)\b[^\n;&|]*"
)
FEATS = re.compile(r"--features[= ]+([A-Za-z0-9_,./\-]+)")
PKGS = re.compile(r"(?:-p|--package)[= ]+([A-Za-z0-9_.\-]+)")
ALLFEATS = re.compile(r"--all-features")
# `cargo test --test a --test b` runs ONLY a and b. Ignoring this is not a detail:
# `scripts/check-lean-marshal.sh` arms `--features lean-lib` and then names exactly
# two of `dregg-lean-ffi`'s SIX whole-file `#![cfg(feature = "lean-lib")]` probes, so
# a sweep that keys on the feature alone declares the other four covered when nothing
# has ever built them.
NAMED_TARGET = re.compile(r"--(?:test|bench)[= ]+([A-Za-z0-9_.\-]+)")
# `--lib`/`--bins`/`--doc` with no `--test` selects no integration-test target at all.
ONLY_NON_TEST = re.compile(r"--(?:lib|bins|doc)\b")
LINE_CONT = re.compile(r"\\\s*\n\s*")
SCRIPT_CALL = re.compile(r"\b(?:bash\s+|sh\s+|\./)?(scripts/[A-Za-z0-9_.\-]+\.sh)\b")


def decomment(text: str) -> str:
    """Drop whole-line `#` comments.

    ⚠ LOAD-BEARING. A `cargo test --features …` inside a COMMENT is not an
    invocation. Scanning comments made `scripts/test-gauntlet.sh` — which appears in
    `.github/workflows/armed-teeth.yml` only as prose in the header, and which NO
    workflow invokes — look like a live CI caller, and hid every target that only
    the gauntlet arms.
    """
    return "\n".join(l for l in text.splitlines() if not l.lstrip().startswith("#"))


def cargo_metadata() -> dict:
    out = subprocess.run(
        ["cargo", "metadata", "--format-version", "1"],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    if out.returncode != 0:
        print(f"::error::cargo metadata failed: {out.stderr[-2000:]}", file=sys.stderr)
        sys.exit(2)
    return json.loads(out.stdout)


def workflow_test_invocations() -> list[dict]:
    """Every `cargo test` / `nextest run` a workflow can actually reach, as records.

    ⚠ THESE MUST BE EVALUATED PER-INVOCATION, NEVER UNIONED. A union says a target is
    covered when invocation A puts it in scope and a DIFFERENT invocation B activates
    its feature — which is exactly the hole that hid four of `dregg-lean-ffi`'s six
    `#![cfg(feature = "lean-lib")]` probes: `cargo test --workspace` has them in scope
    but not armed, and `scripts/check-lean-marshal.sh` arms `lean-lib` while naming
    only two of them with `--test`. Neither invocation runs the other four; a union of
    the two claims all six are covered.
    """
    invocations: list[dict] = []

    texts: list[str] = []
    wf_dir = REPO / ".github" / "workflows"
    for wf in sorted(wf_dir.glob("*.yml")) + sorted(wf_dir.glob("*.yaml")):
        body = wf.read_text(encoding="utf-8", errors="replace")
        texts.append(body)
        # A workflow that INVOKES a script inherits that script's cargo test calls.
        for sc in sorted(set(SCRIPT_CALL.findall(decomment(body)))):
            f = REPO / sc
            if f.is_file():
                texts.append(f.read_text(encoding="utf-8", errors="replace"))

    for body in texts:
        for cmd in CARGO_TEST.findall(LINE_CONT.sub(" ", decomment(body))):
            # Everything after a bare `--` is passed to the test harness, not cargo.
            cargo_part = cmd.split(" -- ", 1)[0]
            pkgs = set(PKGS.findall(cargo_part))
            named = set(NAMED_TARGET.findall(cargo_part))
            if named:
                scope: set[str] | None = named
            elif ONLY_NON_TEST.search(cargo_part):
                scope = set()
            else:
                scope = None
            feats: set[str] = set()
            cross: dict[str, set[str]] = {}
            for grp in FEATS.findall(cargo_part):
                for f in grp.split(","):
                    if not f:
                        continue
                    if "/" in f:
                        p2, f2 = f.split("/", 1)
                        cross.setdefault(p2, set()).add(f2)
                    else:
                        feats.add(f)
            invocations.append(
                {
                    "pkgs": pkgs,            # empty set == workspace-wide
                    "scope": scope,          # None == every target of the package
                    "feats": feats,          # bare --features, apply to `pkgs`
                    "cross": cross,          # pkg/feat form, apply to that pkg
                    "all_features": bool(ALLFEATS.search(cargo_part)),
                }
            )
    return invocations


def gate_of(target: dict, pkg_dir: Path) -> list[str]:
    gate = set(target.get("required-features") or [])
    src = Path(target["src_path"])
    if src.is_file():
        head = src.read_text(encoding="utf-8", errors="replace")[:8000]
        for blob in INNER_CFG.findall(head):
            gate |= set(FEATNAME.findall(blob))
    return sorted(gate)


def never_run() -> list[tuple[str, str, str, list[str], list[str], str]]:
    meta = cargo_metadata()
    members = set(meta["workspace_members"])
    resolved = {n["id"]: set(n["features"]) for n in meta["resolve"]["nodes"]}
    invocations = workflow_test_invocations()

    rows = []
    for p in meta["packages"]:
        if p["id"] not in members:
            continue
        name = p["name"]
        base = set(resolved.get(p["id"], set()))
        declared = set(p.get("features", {}).keys())
        pkg_dir = Path(p["manifest_path"]).parent

        # Per-invocation view of THIS package: (targets in scope, features activated).
        views: list[tuple[set[str] | None, set[str]]] = []
        for inv in invocations:
            if inv["pkgs"] and name not in inv["pkgs"]:
                # A `-p other` run cannot execute this package's targets. Its
                # `pkg/feat` flags still cannot arm a target it does not select.
                continue
            active = set(base)
            if name in inv["cross"]:
                active |= inv["cross"][name]
            if not inv["pkgs"] or name in inv["pkgs"]:
                active |= inv["feats"]
                if inv["all_features"]:
                    active |= declared
            views.append((inv["scope"], active))

        for t in p["targets"]:
            kinds = t.get("kind", [])
            if not any(k in ("test", "bench") for k in kinds):
                continue
            gate = gate_of(t, pkg_dir)
            if not gate:
                continue
            ok = False
            best_missing = gate
            in_scope_anywhere = False
            for scope, active in views:
                if scope is not None and t["name"] not in scope:
                    continue
                in_scope_anywhere = True
                missing = [g for g in gate if g not in active]
                if not missing:
                    ok = True
                    break
                if len(missing) < len(best_missing):
                    best_missing = missing
            if ok:
                continue
            if not in_scope_anywhere:
                why = f"gate={gate}; no cargo test invocation puts this target in scope"
            else:
                why = f"gate={gate} never-activated-by-an-invocation-that-runs-it={best_missing}"
            rows.append((name, kinds[0], t["name"], gate, best_missing, why))
    return sorted(rows)


def known_rows(list_path: Path) -> set[str]:
    rows = set()
    for line in list_path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s.startswith("never-run "):
            continue
        body = s[len("never-run ") :].split("#", 1)[0].strip()
        if body:
            rows.add(body)
    return rows


def reason_index(list_path: Path) -> dict[str, str]:
    """Row -> the trailing `# why` comment, so the run summary can SAY why each
    target does not run instead of merely counting them."""
    out: dict[str, str] = {}
    for line in list_path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s.startswith("never-run "):
            continue
        body = s[len("never-run ") :]
        row, _, why = body.partition("#")
        out[row.strip()] = why.strip() or "(no reason recorded)"
    return out


def key(pkg: str, kind: str, name: str) -> str:
    return f"{pkg} {kind} {name}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--list", type=Path, default=DEFAULT_LIST)
    ap.add_argument("--print-dark", action="store_true")
    ap.add_argument("--explain", action="store_true")
    ap.add_argument(
        "--summary",
        action="store_true",
        help="also write the full enumeration to $GITHUB_STEP_SUMMARY",
    )
    args = ap.parse_args()

    rows = never_run()
    found = {key(p, k, n) for p, k, n, _, _, _ in rows}

    if args.print_dark or args.explain:
        for p, k, n, gate, missing, why in rows:
            print(f"never-run {key(p,k,n)}" + (f"   # {why}" if args.explain else ""))
        return 0

    if not args.list.is_file():
        print(f"::error::allowlist not found: {args.list}", file=sys.stderr)
        return 2

    known = known_rows(args.list)
    new = sorted(found - known)
    stale = sorted(known - found)

    # ── VISIBILITY, WHICH IS THE WHOLE POINT ─────────────────────────────────
    # A ratchet that only speaks when it is violated leaves the STANDING set as
    # invisible as it was before — and the standing set is 63 guards nobody can
    # see. So the enumeration is written to the run summary EVERY run, green or
    # not: a human reading a CI run can then name which guards did not execute
    # and why, instead of reading a checkmark that silently covers them.
    if args.summary and os.environ.get("GITHUB_STEP_SUMMARY"):
        reasons = reason_index(args.list)
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as fh:
            fh.write(f"### Targets that cannot execute ({len(found)})\n\n")
            fh.write(
                "These test targets compile and are wired, and **no workflow can run them**. "
                "Cargo prints nothing at all for a target whose `required-features` are off, and "
                "a whole-file `#![cfg]` target reports `ok. 0 passed` — both read as green.\n\n"
            )
            fh.write("| package | target | gate | why it does not run |\n")
            fh.write("|---|---|---|---|\n")
            for pkg, kind, name, gate, _missing, _why in rows:
                note = reasons.get(key(pkg, kind, name), "**UNTRIAGED — new this run**")
                fh.write(f"| `{pkg}` | `{name}` ({kind}) | `{','.join(gate)}` | {note} |\n")
            fh.write(
                "\nReproduce: `python3 scripts/check-never-run-targets.py --explain`\n"
            )

    if new:
        print("::error::a test target can NEVER EXECUTE and is not on the known list.")
        print("::error::cargo prints NOTHING for a target whose required-features are off, and a")
        print("::error::whole-file #![cfg] target reports `ok. 0 passed` — both read as green.")
        for r in new:
            why = next(w for p, k, n, _, _, w in rows if key(p, k, n) == r)
            print(f"  NEW NEVER-RUN: {r}   ({why})")
        print()
        print("ARM IT (a workflow that passes the feature to a `cargo test`), or add a row to")
        print(f"{args.list} saying WHY and WHO owns it:")
        print("    never-run <package> <kind> <name>   # why, and what arms it instead")
        print()
        print("Reproduce locally:  python3 scripts/check-never-run-targets.py --explain")

    if stale:
        print("::error::these `never-run` rows are EXECUTABLE again. Delete them — a stale")
        print("::error::allowlist is how the next un-runnable guard gets waved through.")
        for r in stale:
            print(f"  NO LONGER NEVER-RUN: {r}")

    if new or stale:
        return 1

    print(f"never-run sweep: {len(found)} known-unrunnable target(s), 0 new, 0 stale.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
