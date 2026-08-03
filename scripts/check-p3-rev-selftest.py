#!/usr/bin/env python3
"""Refuse+anchor harness for scripts/check-p3-rev.sh.

Builds a pristine scratch copy of every file the gate reads, proves it PASSES
(anchor), then applies one mutation at a time and proves each REFUSES with the
RIGHT diagnosis.
"""
import os, shutil, subprocess, sys, tempfile

REPO = "/Users/ember/dev/breadstuffs"
FILES = [
    "scripts/check-p3-rev.sh",
    "scripts/p3-rev.env",
    "Cargo.toml",
    "Cargo.lock",
    ".github/workflows/extension.yml",
    ".github/workflows/publish-sdk-ts.yml",
    ".github/workflows/pages-wasm.yml",
    "wasm/Cargo.toml",
    "circuit-prove/src/recursive_witness_bundle.rs",
]
OLD = "0a4a554e144f4e60107555ea7a11cd9969d6208b"
NEW = "fc3c6dfac26e2082653d2a617a1740446ce33f05"


def pristine():
    d = tempfile.mkdtemp(prefix="p3refute.")
    for rel in FILES:
        dst = os.path.join(d, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(os.path.join(REPO, rel), dst)
    return d


def run(d):
    p = subprocess.run(["bash", os.path.join(d, "scripts/check-p3-rev.sh")],
                       capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr)


def edit(d, rel, fn):
    path = os.path.join(d, rel)
    s = open(path).read()
    open(path, "w").write(fn(s))


results = []


def arm(name, mutate, expect_fail=True, must_contain=None, must_not_contain=None):
    d = pristine()
    try:
        if mutate:
            mutate(d)
        rc, out = run(d)
        ok = (rc != 0) if expect_fail else (rc == 0)
        why = []
        if not ok:
            why.append(f"exit {rc} (expected {'nonzero' if expect_fail else '0'})")
        if must_contain and must_contain not in out:
            ok = False; why.append(f"missing expected text {must_contain!r}")
        if must_not_contain and must_not_contain in out:
            ok = False; why.append(f"contains FORBIDDEN text {must_not_contain!r}")
        results.append((name, ok, rc, out.strip(), "; ".join(why)))
    finally:
        shutil.rmtree(d, ignore_errors=True)


# ---- ANCHOR ------------------------------------------------------------------
arm("A1 pristine (7-hex pin, all mirrors reconciled) PASSES",
    None, expect_fail=False, must_contain="OK: all lockstep")

# ---- REFUSE ------------------------------------------------------------------
arm("R1 one CI mirror reverted to the stale rev",
    lambda d: edit(d, ".github/workflows/publish-sdk-ts.yml", lambda s: s.replace(NEW, OLD)),
    must_contain="publish-sdk-ts.yml pins plonky3 rev")

arm("R2 P3_REV disagrees with what Cargo.lock resolved",
    lambda d: edit(d, "scripts/p3-rev.env", lambda s: s.replace(f"P3_REV={NEW}", f"P3_REV={OLD}")),
    must_contain="but")

arm("R3 Cargo.toml pin is a DIFFERENT full sha than the lock resolved",
    lambda d: edit(d, "Cargo.toml", lambda s: s.replace('rev = "fc3c6df"', f'rev = "{OLD}"')),
    must_contain="is NOT a prefix")

arm("R4 plonky3-recursion rev removed from Cargo.toml entirely",
    lambda d: edit(d, "Cargo.toml", lambda s: s.replace('rev = "fc3c6df"', 'branch = "main"')),
    must_contain="has vanished")

arm("R5 Cargo.lock absent (no resolver)",
    lambda d: os.remove(os.path.join(d, "Cargo.lock")),
    must_contain="Cargo.lock missing")

arm("R6 RECURSION_P3_REV (the VK-hash proving-system id) drifts",
    lambda d: edit(d, "circuit-prove/src/recursive_witness_bundle.rs",
                   lambda s: s.replace(f'RECURSION_P3_REV: &str = "{NEW}"',
                                       f'RECURSION_P3_REV: &str = "{OLD}"')),
    must_contain="RECURSION_P3_REV in recursive_witness_bundle.rs is")

arm("R7 a mirror loses its pin entirely (vanished mirror)",
    lambda d: edit(d, ".github/workflows/extension.yml", lambda s: s.replace(NEW, "HEAD")),
    must_contain="no longer contains the pinned fork rev")

arm("R8 Cargo.lock resolves TWO different shas for the fork",
    lambda d: edit(d, "Cargo.lock",
                   lambda s: s.replace(f"plonky3-recursion?rev=fc3c6df#{NEW}",
                                       f"plonky3-recursion?rev=fc3c6df#{OLD}", 1)),
    must_contain="DIFFERENT shas")

# ⚑ the exact bug this repair exists for
arm("R9 ABBREVIATED pin naming a DIFFERENT rev -> MISMATCH, never 'vanished'",
    lambda d: edit(d, "Cargo.toml", lambda s: s.replace('rev = "fc3c6df"', 'rev = "0a4a554"')),
    must_contain="is NOT a prefix", must_not_contain="has vanished")

# ---- report ------------------------------------------------------------------
width = max(len(n) for n, *_ in results)
allok = True
for name, ok, rc, out, why in results:
    allok &= ok
    print(f"[{'PASS' if ok else 'BROKEN'}] {name:<{width}}  exit={rc}" + (f"   <-- {why}" if why else ""))
print()
print("=" * 78)
print("VERDICT:", "all arms behaved" if allok else "SOME ARMS MISBEHAVED")
print("=" * 78)
if "-v" in sys.argv:
    for name, ok, rc, out, why in results:
        print(f"\n--- {name} (exit {rc}) ---\n{out}")
sys.exit(0 if allok else 1)
