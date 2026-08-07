#!/usr/bin/env python3
"""check-nextest-names.py — every name in .config/nextest.toml still resolves.

── WHY THIS EXISTS ────────────────────────────────────────────────────────────
`.config/nextest.toml` selects tests BY NAME. Names outlive their referents, and
when one does inside this file the damage is not a misleading comment — it is a
silent change to what the test suite RUNS. This repo has now paid for it twice:

  2026-07-15, LOUD.  `effect_vm_descriptor_cutover_harness` was deleted in
    `384d0cd5a` while three filtersets still named it. nextest treats an
    unresolvable `binary()` as a hard config-PARSE error, and it validates EVERY
    profile on EVERY invocation — so `scripts/test-gauntlet.sh` exited nonzero in
    all four modes, HAVING RUN ZERO TESTS, for an unknown number of commits. The
    gauntlet was dead and its exit code was the only thing that said so.

  2026-07-27, SILENT.  Measured against cargo-nextest 0.9.136 / 0.9.137 / 0.9.140
    with a scratch crate, the three operators this file uses do NOT behave alike:

        binary(nope)   -> hard error, exit 96, "didn't match any binary names"
        package(nope)  -> hard error, exit 96, "didn't match any packages"
        test(~nope)    -> SILENT. exit 0. no warning, no output, nothing.

    So nextest self-defends two of three, and `test()` — the operator this file
    uses for 21 of its 35 selectors — is unguarded. A sweep that day found **21 of
    41 `test(~…)` names matched no `fn` anywhere in the workspace**: the whole
    kimchi quarantine, naming tests deleted in `d260028f1` and `136e51446`.

WHAT A DEAD `test()` NAME DOES depends on its polarity, and one direction is
much worse than the other:

  * in a `not (…)` exclusion (default / ci): excludes nothing. The file merely
    states a quarantine that is not in force.
  * in a positive selector (heavy, gpu): the test is silently NOT RUN by the one
    profile that exists to run it — and because default/ci exclude it by that same
    dead name, it simultaneously reappears in the fast gauntlet it was segregated
    out of. For `gpu` the renamed tooth lands in `armed`, i.e. on GPU-less boxes,
    which is the guaranteed-red the gpu/armed split exists to prevent.

── WHAT IT CHECKS, AND HOW SURE IT IS ─────────────────────────────────────────
  binary(N) / package(N)  EXACTLY, from `cargo metadata --no-deps`. No compile.
                          This is strictly better than nextest's own check, which
                          can only fire AFTER the whole workspace has been built.
  test(~N)                against the tree's own `fn` declarations, three tiers:
                            OK    some `fn …N…` is declared  -> resolved
                            WARN  N appears in a .rs but not as a fn name -> could
                                  be macro-generated; reported, does not fail
                            DEAD  N appears in NO .rs file at all -> FAILS
                          Only true absence fails, so a red here is high-confidence
                          and this cannot go off on a `concat_idents!`-style name.

Exit 0 iff every name resolves. `--self-test` proves it can go red.
"""
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONFIG = os.path.join(ROOT, ".config", "nextest.toml")

# Floors. A parser that silently stops finding names must not read as clean —
# the negative-assertion failure mode this whole gate is about. Tripped by
# --self-test as well, so the floor itself is exercised.
MIN_NAMES = 20
MIN_PACKAGES = 100
# If the `fn` index comes back empty or tiny, EVERY test() name resolves to
# nothing and the gate emits a screenful of confident, wrong reds. That is the
# same negative-assertion failure this gate exists to catch, turned on itself —
# so an unusable index is ONE floor failure, never 20 findings.
MIN_FNS = 1000


def strip_comments(text):
    return "\n".join(l for l in text.splitlines() if not l.lstrip().startswith("#"))


def extract(text):
    """-> {'binary': [...], 'package': [...], 'test': [...]} in file order."""
    body = strip_comments(text)
    found = {"binary": [], "package": [], "test": []}
    for kind in found:
        for m in re.finditer(r"\b%s\(\s*[~=]?\s*([A-Za-z0-9_-]+)\s*\)" % kind, body):
            n = m.group(1)
            if n not in found[kind]:
                found[kind].append(n)
    return found


def cargo_names():
    """-> (package names, every target name) from cargo metadata. No compile."""
    out = subprocess.run(
        ["cargo", "metadata", "--no-deps", "--format-version", "1"],
        cwd=ROOT, capture_output=True, text=True,
    )
    if out.returncode != 0:
        print("check-nextest-names: cargo metadata FAILED — cannot resolve anything.")
        print(out.stderr.strip()[-800:])
        sys.exit(2)
    meta = json.loads(out.stdout)
    pkgs, targets = set(), set()
    for p in meta["packages"]:
        pkgs.add(p["name"])
        for t in p["targets"]:
            targets.add(t["name"])
            targets.add(t["name"].replace("-", "_"))
    return pkgs, targets


def source_index():
    """-> (declared fn names, whole .rs corpus) for test-name resolution."""
    rg = subprocess.run(
        ["rg", "--no-messages", "--type", "rust", "-o", "-N", "-I",
         r"fn\s+[A-Za-z0-9_]+", "-g", "!target", "-g", "!metatheory"],
        cwd=ROOT, capture_output=True, text=True,
    )
    fns = set()
    for line in rg.stdout.splitlines():
        parts = line.split()
        if len(parts) == 2:
            fns.add(parts[1])
    corpus = subprocess.run(
        ["rg", "--no-messages", "--type", "rust", "-o", "-N", "-I",
         r"[A-Za-z0-9_]{8,}", "-g", "!target", "-g", "!metatheory"],
        cwd=ROOT, capture_output=True, text=True,
    )
    return fns, set(corpus.stdout.split())


def check(config_text, verbose=True):
    """-> (failures, warnings, names_checked)"""
    names = extract(config_text)
    total = sum(len(v) for v in names.values())
    pkgs, targets = cargo_names()
    fns, corpus = source_index()

    failures, warnings = [], []

    if len(pkgs) < MIN_PACKAGES:
        failures.append(
            f"FLOOR: cargo metadata yielded {len(pkgs)} packages (< {MIN_PACKAGES}); "
            "resolution is not trustworthy, refusing to report clean")
    if total < MIN_NAMES:
        failures.append(
            f"FLOOR: parsed only {total} names from {CONFIG} (< {MIN_NAMES}); "
            "the extractor is probably broken, refusing to report clean")
    if len(fns) < MIN_FNS:
        failures.append(
            f"FLOOR: the `fn` index holds {len(fns)} names (< {MIN_FNS}) — `rg` is "
            "missing or failed. Every test() name would read as DEAD; reporting one "
            "floor failure instead of a screen of false findings.")
        return failures, warnings, total

    for n in names["binary"]:
        if n not in targets:
            failures.append(
                f"binary({n}) — NO such cargo target. nextest hard-errors on this "
                "(exit 96) for EVERY profile, so the whole gauntlet runs zero tests.")
    for n in names["package"]:
        if n not in pkgs:
            failures.append(
                f"package({n}) — NO such workspace package. nextest hard-errors on "
                "this (exit 96) for EVERY profile.")
    for n in names["test"]:
        if any(n in f for f in fns):
            continue
        if any(n in tok for tok in corpus):
            warnings.append(
                f"test(~{n}) — no `fn` declares it, but the name appears in a .rs "
                "file. Possibly macro-generated; confirm it still runs.")
        else:
            failures.append(
                f"test(~{n}) — matches NOTHING in the tree, and nextest reports "
                "this SILENTLY (exit 0). If it is a positive selector, its profile "
                "is not running the test it names.")

    if verbose:
        print(f"names in {os.path.relpath(CONFIG, ROOT)}: "
              f"{len(names['binary'])} binary · {len(names['package'])} package · "
              f"{len(names['test'])} test  (resolved against {len(pkgs)} packages, "
              f"{len(targets)} targets, {len(fns)} fn declarations)")
        for w in warnings:
            print(f"  WARN {w}")
        for f in failures:
            print(f"  FAIL {f}")
    return failures, warnings, total


def self_test():
    """Prove the gate BITES. A negative assertion passes just as happily when the
    reader is broken, so this injects each failure mode and demands a red."""
    print("── self-test: the gate must go RED on each injected fault ──")
    real = open(CONFIG).read()
    ok = True

    def inject(old, new):
        """Mutate the first LIVE (non-comment) occurrence only.

        ⚠ A plain str.replace(…, 1) is WRONG here and this self-test caught it doing
        the wrong thing: `package(dregg-circuit-prove)` appears first in the header
        PROSE, so the injection landed on a comment, `check()` stripped it, and the
        gate was pronounced "blind" to a fault that had never been injected. A
        self-test that mutates a comment tests nothing and reports a false alarm —
        the mirror image of the bug this whole file is about.
        """
        out, done = [], False
        for line in real.splitlines(keepends=True):
            if not done and old in line and not line.lstrip().startswith("#"):
                line = line.replace(old, new, 1)
                done = True
            out.append(line)
        return ("".join(out) if done else real)

    cases = [
        ("dead binary()",
         inject("binary(descriptor_leaf_recursion)", "binary(zzz_no_such_binary_xyz)"),
         "zzz_no_such_binary_xyz"),
        ("dead test() — THE SILENT ONE nextest never reports",
         inject("test(~k_fold_turn_chain_proves_and_verifies)", "test(~zzz_no_such_test_xyz)"),
         "zzz_no_such_test_xyz"),
        ("dead package()",
         inject("package(dregg-circuit-prove)", "package(zzz-no-such-package)"),
         "zzz-no-such-package"),
    ]
    for label, mutated, needle in cases:
        if mutated == real:
            print(f"  FAIL [{label}] injection did not apply — the anchor string is "
                  "gone from the config. Update this self-test.")
            ok = False
            continue
        fails, _, _ = check(mutated, verbose=False)
        if any(needle in f for f in fails):
            print(f"  ok   [{label}] -> caught")
        else:
            print(f"  FAIL [{label}] -> NOT caught. The gate is blind to this fault.")
            ok = False

    # The floor must bite too: an extractor that finds nothing must not read clean.
    fails, _, _ = check("[profile.default]\nslow-timeout = { period = \"45s\" }\n",
                        verbose=False)
    if any("FLOOR" in f for f in fails):
        print("  ok   [empty config / dead extractor] -> caught by the floor")
    else:
        print("  FAIL [empty config / dead extractor] -> NOT caught; the floor is dead")
        ok = False

    # And it must be GREEN on the real file, or a red here means nothing.
    fails, _, n = check(real, verbose=False)
    if fails:
        print(f"  FAIL [real config] -> {len(fails)} failure(s); a gate that is red "
              "at rest cannot signal anything. First: " + fails[0])
        ok = False
    else:
        print(f"  ok   [real config] -> clean, {n} names resolved")

    print("self-test PASSED" if ok else "self-test FAILED")
    return 0 if ok else 1


def main():
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    if not os.path.exists(CONFIG):
        print(f"check-nextest-names: {CONFIG} does not exist")
        sys.exit(2)
    failures, warnings, total = check(open(CONFIG).read())
    if failures:
        print(f"\n{len(failures)} unresolvable name(s) in .config/nextest.toml.")
        print("Fix the config (or restore the test); do NOT delete the gate.")
        sys.exit(1)
    print(f"all {total} names resolve"
          + (f" ({len(warnings)} warning(s))" if warnings else ""))
    sys.exit(0)


if __name__ == "__main__":
    main()
