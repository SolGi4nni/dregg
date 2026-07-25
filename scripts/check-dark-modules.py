#!/usr/bin/env python3
"""check-dark-modules.py — a tracked .rs file that NO `mod` declaration reaches.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
`.github/dark-targets.txt` + the `dark-target ratchet` catch a target that FAILS TO
COMPILE. They cannot catch a file rustc NEVER OPENS. Those two failures look nothing
alike to cargo and identical to a reader: in both cases every `#[test]` in the file
is a falsifier that cannot fire.

The difference is that an unreferenced file is SILENT. It emits no diagnostic, it is
not a target, `--keep-going` never names it, and `cargo test -- <filter>` over its
tests prints `0 filtered out ... ok` — a GREEN report for a test run that executed
nothing. That exact sequence produced a live security hole on 2026-07-25:
`eth-lightclient`'s `bridge_lc_ffi` ETH light-client verification bridge had never
been compiled, and `cargo test --lib -- bridge_lc_ffi` matched 0 of its 24 tests and
reported success.

Measured at the commit that added this gate: 3,964 tracked `.rs`, THREE of them dark
in this sense —
  * `circuit/src/xmss.rs`         526 lines of XMSS one-time-signature key tree
  * `sdk/src/fhegg.rs`            199 lines, wired 07-17 and un-wired 07-20 as
                                  collateral in an ML-DSA commit; the `fhegg` feature
                                  stayed in `default`, so the dep was still compiled
  * `dregg-dsl/src/gen_diff_test.rs`  238 lines, dark since the repo's root commit
                                  and RED (3 E0004s) the moment it was wired

═══ WHAT COUNTS AS REACHABLE ══════════════════════════════════════════════════════
A file is reachable if it is a TARGET ROOT (cargo opens it directly) or a MODULE some
in-crate file declares.

  TARGET ROOTS   `build.rs`, `src/lib.rs`, `src/main.rs`, `src/bin/*.rs`,
                 `src/bin/*/main.rs`, `{tests,benches,examples}/*.rs` and
                 `{tests,benches,examples}/*/main.rs`, plus every explicit
                 `path = "…"` in the crate's Cargo.toml.
  MODULES        a `mod NAME;` / `pub mod NAME;` / `mod NAME { … }` anywhere in the
                 SAME CRATE names `…/NAME.rs` or `…/NAME/mod.rs`, or a
                 `#[path = "…"]` attribute resolves to the file.

The mod-name match is per-crate and not per-directory, so it is DELIBERATELY LOOSE: a
`mod foo;` in the wrong directory still counts. This gate is not a module resolver and
does not try to be one. It answers exactly one question — is this file mentioned AT ALL
— because that is the question a dark file fails, and a loose matcher has no false
positives to argue with.

═══ THE RATCHET ═══════════════════════════════════════════════════════════════════
Two-sided, sharing `.github/dark-targets.txt` with the compile-fail ratchet. File rows
are prefixed `file ` so the two readers partition the same list:

    file some/crate/src/thing.rs   # why it is deliberately uncompiled

A dark file NOT on the list fails. A row on the list that is now reachable ALSO fails —
a stale allowlist is how the next one gets waved through.

⚠ IT SWEEPS THE INDEX, NOT THE WORKING TREE. `git ls-files` is the file set, so a NEW
file you have not `git add`ed is INVISIBLE to a local run — the first canary written for
this gate was an untracked probe and the gate reported CLEAN over it. In CI that is
correct and total (a checkout of HEAD has nothing untracked), but locally: `git add`
first, then sweep. Both directions were then re-verified with a TRACKED probe.

Usage:  python3 scripts/check-dark-modules.py [--list PATH] [--print-dark]
Exit:   0 clean · 1 ratchet violation · 2 usage/environment error
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_LIST = REPO / ".github" / "dark-targets.txt"

# `mod foo;`, `pub mod foo;`, `pub(crate) mod foo {`, `#[cfg(x)] mod foo;` — the
# leading-context-agnostic form. `\bmod\s+(ident)\s*[;{]` also matches inside a
# string or a comment, which is fine and intentional: a name MENTIONED as a module
# anywhere in the crate is enough to clear this gate. Under-reporting a dark file is
# the failure that matters; a comment naming a real module is not a dark file.
MOD_RE = re.compile(r"\bmod\s+([A-Za-z_][A-Za-z0-9_]*)\s*[;{]")
# `#[path = "…"]` / `#[cfg_attr(…, path = "…")]`
PATH_ATTR_RE = re.compile(r'\bpath\s*=\s*"([^"]+)"')
# `include!("…")` / `include_str!` — a file pulled in textually is compiled too.
INCLUDE_RE = re.compile(r'\binclude(?:_str|_bytes)?!\s*\(\s*"([^"]+)"')
# Cargo.toml `path = "…"` (targets AND path-deps; both make the file reachable).
CARGO_PATH_RE = re.compile(r'^\s*path\s*=\s*"([^"]+)"', re.MULTILINE)


def tracked_rs_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.rs"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    # `git ls-files` reads the INDEX; a live lane's staged-but-not-committed deletion
    # is still listed and is not on disk. CI sees HEAD, where such a file is simply
    # gone — so skipping absent files makes a local run agree with CI instead of
    # reporting a co-tenant's in-flight `git rm` as a new dark file.
    return [Path(p) for p in out.split("\0") if p and (REPO / p).is_file()]


def crate_roots() -> set[Path]:
    """Every directory holding a tracked Cargo.toml."""
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", "*Cargo.toml"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    roots = {Path(p).parent for p in out.split("\0") if p}
    roots.discard(Path("."))
    return roots


_OWNER_CACHE: dict[Path, Path | None] = {}


def owning_crate(f: Path, roots: set[Path]) -> Path | None:
    """The INNERMOST crate root containing `f` — walk up, first hit wins.

    Innermost matters: `starbridge-v2/vendor/pathfinder_simd/` is its own crate
    inside `starbridge-v2/`, and its files must be checked against ITS mod set.
    """
    d = f.parent
    if d in _OWNER_CACHE:
        return _OWNER_CACHE[d]
    cur = d
    found: Path | None = None
    while True:
        if cur in roots:
            found = cur
            break
        if cur == Path("."):
            break
        cur = cur.parent
    _OWNER_CACHE[d] = found
    return found


def target_roots(crate: Path) -> set[Path]:
    """Files cargo opens directly for this crate, without any `mod` line."""
    roots: set[Path] = set()
    # `build.rs` at the crate root is AUTO-DISCOVERED by cargo and compiled as its
    # own host target. No `mod` line names it and none ever will.
    for rel in ("build.rs", "src/lib.rs", "src/main.rs"):
        roots.add(crate / rel)
    for sub, nested in (("src/bin", True), ("tests", True), ("benches", True), ("examples", True)):
        d = REPO / crate / sub
        if not d.is_dir():
            continue
        for entry in d.iterdir():
            if entry.is_file() and entry.suffix == ".rs":
                roots.add(crate / sub / entry.name)
            elif nested and entry.is_dir():
                roots.add(crate / sub / entry.name / "main.rs")
    cargo = REPO / crate / "Cargo.toml"
    if cargo.is_file():
        text = cargo.read_text(encoding="utf-8", errors="replace")
        for raw in CARGO_PATH_RE.findall(text):
            if raw.endswith(".rs"):
                roots.add((crate / raw).resolve().relative_to(REPO) if (crate / raw).is_absolute() else Path(os.path.normpath(crate / raw)))
    return roots


def scan(files: list[Path]) -> tuple[dict[Path, set[str]], set[Path]]:
    """Per-crate declared mod names, plus files named by an explicit path/include."""
    roots = crate_roots()
    mods_by_crate: dict[Path, set[str]] = {}
    explicit: set[Path] = set()
    for f in files:
        abs_f = REPO / f
        try:
            text = abs_f.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        crate = owning_crate(f, roots)
        if crate is not None:
            mods_by_crate.setdefault(crate, set()).update(MOD_RE.findall(text))
        for raw in PATH_ATTR_RE.findall(text) + INCLUDE_RE.findall(text):
            if not raw.endswith(".rs"):
                continue
            explicit.add(Path(os.path.normpath(f.parent / raw)))
            # `#[path]` on an inline `mod x { … }` is relative to the module dir too.
            explicit.add(Path(os.path.normpath(f.parent / f.stem / raw)))
    return mods_by_crate, explicit


def dark_files() -> list[Path]:
    files = tracked_rs_files()
    roots = crate_roots()
    mods_by_crate, explicit = scan(files)

    all_targets: set[Path] = set()
    for crate in {c for c in (owning_crate(f, roots) for f in files) if c is not None}:
        all_targets |= target_roots(crate)

    dark: list[Path] = []
    for f in files:
        if f in all_targets or f in explicit:
            continue
        crate = owning_crate(f, roots)
        if crate is None:
            # Outside every Cargo.toml — cargo cannot reach it by any route.
            dark.append(f)
            continue
        declared = mods_by_crate.get(crate, set())
        name = f.parent.name if f.name == "mod.rs" else f.stem
        if name not in declared:
            dark.append(f)
    return sorted(dark)


def known_rows(list_path: Path) -> list[str]:
    rows = []
    for line in list_path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s.startswith("file "):
            continue
        rows.append(s[len("file ") :].split("#", 1)[0].strip())
    return sorted(set(r for r in rows if r))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--list", type=Path, default=DEFAULT_LIST)
    ap.add_argument("--print-dark", action="store_true", help="print the dark set and exit 0")
    args = ap.parse_args()

    dark = {str(p) for p in dark_files()}

    if args.print_dark:
        for p in sorted(dark):
            print(p)
        return 0

    if not args.list.is_file():
        print(f"::error::allowlist not found: {args.list}", file=sys.stderr)
        return 2

    known = set(known_rows(args.list))
    new = sorted(dark - known)
    stale = sorted(known - dark)

    if new:
        print("::error::a tracked .rs file is DARK — no `mod` declaration, no `[[bin]]`, no `path =`.")
        print("::error::rustc has never opened it, so every #[test] in it is a falsifier that")
        print("::error::cannot fire, and `cargo test -- <its filter>` reports `0 tests ... ok`.")
        for p in new:
            print(f"  NEW DARK FILE: {p}")
        print()
        print("WIRE IT (`mod` line / `[[bin]]` / `#[path]`) or DELETE IT. If it is genuinely")
        print(f"not meant to compile, add a row to {args.list}:")
        print("    file <path>   # why, and who owns it")
        print()
        print("Reproduce locally:  python3 scripts/check-dark-modules.py --print-dark")

    if stale:
        print("::error::these `file` rows are REACHABLE again. Delete them — a stale allowlist is")
        print("::error::how the next dark file gets waved through.")
        for p in stale:
            print(f"  NO LONGER DARK: {p}")

    if new or stale:
        return 1

    print(f"mod-declaration sweep: {len(dark)} known-dark file(s), 0 new, 0 stale.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
