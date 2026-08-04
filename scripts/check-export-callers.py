#!/usr/bin/env python3
"""check-export-callers.py — a verified Lean gate that SHIPS in the archive and that NO Rust file
ever names.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
`@[export foo]` on a Lean decision, plus an `import` line in `metatheory/Dregg2/FFI.lean`, is
enough to put `foo` in `libdregg_lean.a`. Nothing else is required, and in particular **no caller
is required**. So a gate can be authored, proved, `#assert_axioms`-ed, documented as "THE GATE",
compiled into every binary the node links — and decide nothing, forever, silently.

There is no diagnostic for this. It is not dead code (Lean emitted it and the linker kept it), it
is not an unused import, it breaks no build, and the module's own theorems stay green because they
are theorems about a function, not about a call. `check-dark-modules.py` catches a `.rs` file
rustc never opens; this catches a Lean DECISION rustc never asks.

Measured 2026-08-03, by a census of `dregg_mina_*` exports against their Rust bindings:

    lc_verify 4 · better_tip 4 · proof_chain_ok 3 · state_hash_word_ok 3 · checkpoint_advance 3
    head_advance 3 · wrap_challenges 3 · wrap_shape_ok 3 · account_state_ok 2 · wrap_ft_eval 2
    ────────────────────────────────────────────────────────────────────────────────────────────
    deferral_ok 0 · vrf_threshold_satisfied 0 · window_transition_ok 0

`dregg_mina_deferral_ok` is the sharp one. It is `Dregg2.Circuit.Emit.PastaIpaDeferral`'s §5 gate —
the object that decides whether a batch of deferred IPA accumulator claims may be ACCEPTED — and
its `d=` field ("the batched MSM was evaluated and found to vanish") was read straight off a wire
string. With no caller, nothing ever computed that MSM, so `opening_is_vacuous_when_sg_is_free`
applied to the live runtime: an undischarged accumulator is not a weakened check, it is NO check.
The gate was closed on 2026-08-04 by `dregg_bridge::mina_accumulator_discharge`.

═══ WHAT COUNTS ═══════════════════════════════════════════════════════════════════
SHIPPED — an `@[export NAME]` whose module is in the transitive `import` closure of
`metatheory/Dregg2/FFI.lean`. That closure is the ship condition: a module rooted only in
`Dregg2.lean` ELABORATES and emits no `:c` facet, so its symbol never enters the archive and
"nobody calls it" is not a finding. Computed statically from `import` lines — no build needed.

NAMED — the export's name (or `NAME_str`, the C string bridge) appears in a tracked `.rs` file
OTHER than `dregg-lean-ffi/build.rs`. The build script names every symbol it PROBES, so counting it
would make every shipped export look wired; that is the exact confusion this gate exists to
prevent.

A shipped export that is not named is a RED. That is the whole rule, and it is deliberately the
weaker of the two available bars: it asks "is there a binding at all", not "is the binding
reached". The stronger question — is the wrapper called from a CONSUMER crate — is reported in the
second column (`consumers`) so a reader can see it, and is NOT ratcheted, because a gate should
red on a fact it can state exactly rather than on a heuristic about call graphs.

═══ THE RATCHET ═══════════════════════════════════════════════════════════════════
`.github/uncalled-exports.txt`, one row per deliberately-uncalled export:

    dregg_some_export   # why nothing calls it, and what would

An uncalled export NOT on the list fails. A row on the list that is NOW called ALSO fails — a stale
allowlist is how the next one gets waved through.

⚠ IT SWEEPS THE INDEX, NOT THE WORKING TREE (`git ls-files`), same as `check-dark-modules.py`: a
NEW `.rs` you have not `git add`ed is INVISIBLE, so a freshly written caller reads as absent. In CI
that is correct and total; locally, `git add` first.

Usage:  python3 scripts/check-export-callers.py [--list PATH] [--print-all] [--self-test]
Exit:   0 clean · 1 ratchet violation · 2 usage/environment error
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_LIST = os.path.join(ROOT, ".github", "uncalled-exports.txt")
FFI_ROOT = os.path.join(ROOT, "metatheory", "Dregg2", "FFI.lean")
METATHEORY = os.path.join(ROOT, "metatheory")

EXPORT_RE = re.compile(r"@\[\s*export\s+([A-Za-z_][A-Za-z0-9_']*)\s*\]")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.M)

# The build script names every symbol it PROBES with `archive_exports(...)`. Naming is not wiring.
PROBE_FILES = {"dregg-lean-ffi/build.rs"}


def tracked(patterns: list[str]) -> list[str]:
    out = subprocess.run(
        ["git", "-C", ROOT, "ls-files", "-z", *patterns],
        capture_output=True,
        text=True,
        check=True,
    )
    return [p for p in out.stdout.split("\0") if p]


def module_path(mod: str) -> str | None:
    """`Dregg2.Circuit.Emit.PastaIpaDeferral` -> metatheory/Dregg2/Circuit/Emit/PastaIpaDeferral.lean"""
    p = os.path.join(METATHEORY, *mod.split(".")) + ".lean"
    return p if os.path.isfile(p) else None


def ffi_closure() -> set[str]:
    """Every module transitively imported by `Dregg2/FFI.lean`, plus FFI itself."""
    seen: set[str] = set()
    stack = ["Dregg2.FFI"]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = module_path(mod)
        if p is None:
            continue
        with open(p, "r", encoding="utf-8", errors="replace") as fh:
            src = fh.read()
        for imp in IMPORT_RE.findall(src):
            if imp not in seen:
                stack.append(imp)
    return seen


def exports_by_module() -> dict[str, list[str]]:
    """{module -> [export names]} over every tracked .lean under metatheory/."""
    out: dict[str, list[str]] = {}
    for rel in tracked(["metatheory/**/*.lean"]):
        if "/.lake/" in rel:
            continue
        with open(os.path.join(ROOT, rel), "r", encoding="utf-8", errors="replace") as fh:
            src = fh.read()
        names = EXPORT_RE.findall(src)
        if not names:
            continue
        mod = os.path.relpath(os.path.join(ROOT, rel), METATHEORY)[: -len(".lean")]
        out.setdefault(mod.replace(os.sep, "."), []).extend(names)
    return out


def rust_mentions(names: set[str]) -> dict[str, list[str]]:
    """{export -> [tracked .rs files that name it]}, excluding the probe file."""
    hits: dict[str, set[str]] = {n: set() for n in names}
    for rel in tracked(["*.rs"]):
        if rel in PROBE_FILES:
            continue
        try:
            with open(os.path.join(ROOT, rel), "r", encoding="utf-8", errors="replace") as fh:
                src = fh.read()
        except OSError:
            continue
        for n in names:
            if n in src:
                hits[n].add(rel)
    return {k: sorted(v) for k, v in hits.items()}


def read_list(path: str) -> dict[str, str]:
    allow: dict[str, str] = {}
    if not os.path.isfile(path):
        return allow
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            body = line.split("#", 1)[0].strip()
            if not body:
                continue
            allow[body.split()[0]] = line.split("#", 1)[1].strip() if "#" in line else ""
    return allow


def survey(list_path: str):
    closure = ffi_closure()
    by_mod = exports_by_module()
    shipped: dict[str, str] = {}
    for mod, names in by_mod.items():
        if mod in closure:
            for n in names:
                shipped[n] = mod
    probe_names = set(shipped) | {f"{n}_str" for n in shipped}
    mentions = rust_mentions(probe_names)

    rows = []
    for name, mod in sorted(shipped.items()):
        files = sorted(set(mentions.get(name, [])) | set(mentions.get(f"{name}_str", [])))
        consumers = [f for f in files if not f.startswith("dregg-lean-ffi/")]
        rows.append((name, mod, files, consumers))
    return rows, read_list(list_path)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", default=DEFAULT_LIST)
    ap.add_argument("--print-all", action="store_true")
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="prove the gate can go RED: inject a shipped export that nothing names.",
    )
    args = ap.parse_args()

    if args.self_test:
        # A name no `.rs` in this tree contains, checked against the same matcher.
        canary = "dregg_selftest_export_no_caller_zzz"
        found = rust_mentions({canary, canary + "_str"})
        named = bool(found[canary] or found[canary + "_str"])
        if named:
            print(f"SELF-TEST FAIL: the canary {canary} is named in {found}")
            return 1
        # …and the positive control: an export that IS named must read as named.
        control = "dregg_mina_lc_verify"
        ctrl = rust_mentions({control, control + "_str"})
        if not (ctrl[control] or ctrl[control + "_str"]):
            print(f"SELF-TEST FAIL: the control {control} reads as uncalled")
            return 1
        print(
            f"SELF-TEST PASS: an unnamed export reads as uncalled and {control} reads as called "
            f"({len(ctrl[control]) + len(ctrl[control + '_str'])} files)."
        )
        return 0

    rows, allow = survey(args.list)
    uncalled = [(n, m, c) for (n, m, f, c) in rows if not f]
    binding_only = [(n, m) for (n, m, f, c) in rows if f and not c]

    print(f"shipped exports (in the Dregg2.FFI import closure): {len(rows)}")
    print(f"  with a Rust binding : {len(rows) - len(uncalled)}")
    print(f"  UNCALLED            : {len(uncalled)}")
    print(f"  binding-only (no consumer crate outside dregg-lean-ffi): {len(binding_only)}")

    if args.print_all:
        for name, mod, files, consumers in rows:
            print(f"  {len(files):>2} rs / {len(consumers):>2} consumer  {name:<44} {mod}")

    bad = 0
    for name, mod, _ in uncalled:
        if name in allow:
            continue
        bad += 1
        print(
            f"UNCALLED EXPORT: {name}  ({mod})\n"
            f"    it is in the Dregg2.FFI import closure, so it SHIPS in libdregg_lean.a, and no\n"
            f"    tracked .rs file names it. Wire it, delete it, or put it on {os.path.relpath(args.list, ROOT)}\n"
            f"    with the reason nothing calls it."
        )
    stale = [n for n in allow if any(n == r[0] and r[2] for r in rows)]
    for n in stale:
        bad += 1
        print(
            f"STALE ALLOWLIST ROW: {n} is now named by Rust — remove it from "
            f"{os.path.relpath(args.list, ROOT)}."
        )
    unknown = [n for n in allow if not any(n == r[0] for r in rows)]
    for n in unknown:
        bad += 1
        print(
            f"STALE ALLOWLIST ROW: {n} is not a shipped export at all (renamed, deleted, or no "
            f"longer imported by Dregg2/FFI.lean)."
        )

    if bad:
        print(f"\nFAIL: {bad} problem(s).")
        return 1
    print("\nCLEAN: every shipped Lean export is named by Rust, or is on the ratchet with a reason.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as e:
        print(f"environment error: {e}", file=sys.stderr)
        sys.exit(2)
