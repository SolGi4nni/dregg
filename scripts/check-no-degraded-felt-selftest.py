#!/usr/bin/env python3
"""Refuse+anchor self-test for the faithful-commitment ast-grep rules.

⚑ It exercises the REAL rule file. `.ast-grep/rules/faithful-commitment-felt.yml` is
copied into a scratch tree with ONLY its `files:` scopes re-pointed at a synthetic
producer; every `rule:` clause is the shipped one. A self-test that re-typed the rule
would be testing its own reconstruction — green in the scratchpad, blind on the tree.

Why this exists: on 2026-08-02 the `degraded-felt-commitment` rule was narrowed to stop
matching `#[cfg(test)]` bodies. That exclusion is the kind of change that can quietly
buy an escape hatch (rename a `mod` to `tests` and walk a production fold past the
gate), so both poles are pinned here — what it still REFUSES, and what it now PERMITS.

Usage:  python3 scripts/check-no-degraded-felt-selftest.py [-v]
Exit:   0 = every arm behaved; 1 = an arm misbehaved; 2 = ast-grep missing.
"""
import os, re, shutil, subprocess, sys, tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RULE = os.path.join(REPO, ".ast-grep/rules/faithful-commitment-felt.yml")
DEMO_REL = "src/demo.rs"

SG = shutil.which("ast-grep") or shutil.which("sg")
if not SG:
    print("check-no-degraded-felt-selftest: FATAL — ast-grep ('sg') not on PATH.", file=sys.stderr)
    sys.exit(2)


def scratch(rust_src):
    """Materialise the REAL rules with their scope re-pointed at a synthetic producer."""
    d = tempfile.mkdtemp(prefix="feltselftest.")
    os.makedirs(os.path.join(d, "rules"), exist_ok=True)
    os.makedirs(os.path.join(d, "src"), exist_ok=True)
    text = open(RULE).read()
    # Replace each `files:` block (a flat list of quoted paths, possibly with comments)
    # with a single entry pointing at the demo. Rule bodies are untouched.
    out, i = [], 0
    for line in text.split("\n"):
        if re.match(r"^files:\s*$", line):
            out.append("files:")
            out.append(f'  - "{DEMO_REL}"')
            i = 1
            continue
        if i == 1:
            if re.match(r'^\s*(-\s*".*"|#.*)\s*$', line) or not line.strip():
                continue  # swallow the old scope list + its comments
            i = 0
        out.append(line)
    open(os.path.join(d, "rules/faithful-commitment-felt.yml"), "w").write("\n".join(out))
    open(os.path.join(d, "sgconfig.yml"), "w").write("ruleDirs:\n  - rules\n")
    open(os.path.join(d, DEMO_REL), "w").write(rust_src)
    return d


def flagged(rust_src):
    """Return the set of 1-based line numbers ast-grep reports as errors."""
    d = scratch(rust_src)
    try:
        p = subprocess.run([SG, "scan", "--config", os.path.join(d, "sgconfig.yml"),
                            os.path.join(d, DEMO_REL)], capture_output=True, text=True, cwd=d)
        return {int(m) for m in re.findall(r"demo\.rs:(\d+):", p.stdout + p.stderr)}
    finally:
        shutil.rmtree(d, ignore_errors=True)


results = []


def arm(name, src, expect):
    got = flagged(src)
    ok = got == set(expect)
    results.append((name, ok, sorted(got), sorted(expect)))


# ── REFUSE: production folds, every alias spelling ───────────────────────────────
arm("R1 production fold_bytes32_to_bb is REFUSED",
    "fn p(x: &[u8;32]) -> B {\n    fold_bytes32_to_bb(x)\n}\n", [2])
arm("R2 alias fold_bytes32 (cap-tree target) is REFUSED",
    "fn p(x: &[u8;32]) -> B {\n    cap_root::fold_bytes32(x)\n}\n", [2])
arm("R3 alias fold_value32 (fields-root value) is REFUSED",
    "fn p(x: &[u8;32]) -> B {\n    fold_value32(x)\n}\n", [2])
arm("R4 replicated [X; 8] splat is REFUSED",
    "fn p(r: B) -> [B;8] {\n    [r; 8]\n}\n", [2])

# ── REFUSE: the escapes the cfg(test) exclusion must NOT open ────────────────────
arm("R5 a `mod tests` WITHOUT #[cfg(test)] buys NO escape",
    "mod tests {\n    fn s(x: &[u8;32]) -> B {\n        fold_bytes32_to_bb(x)\n    }\n}\n", [3])
arm("R6 #[cfg(feature=..)] is NOT #[cfg(test)] — still REFUSED",
    '#[cfg(feature = "gpu")]\nmod g {\n    fn s(x: &[u8;32]) -> B {\n'
    "        fold_bytes32_to_bb(x)\n    }\n}\n", [4])
arm("R7 a #[test] fn at module top level (not in a cfg(test) mod) is REFUSED",
    "#[test]\nfn t() {\n    let v = fold_bytes32_to_bb(&y);\n}\n", [3])

# ── ANCHOR: what the narrowing is FOR — the anti-vacuity witnesses ───────────────
arm("A1 the legacy-exhibit fold inside #[cfg(test)] is PERMITTED",
    "#[cfg(test)]\nmod tests {\n    fn legacy_is_not_current() {\n"
    "        let legacy = fold_bytes32_to_bb(&n);\n        assert_ne!(cur, legacy);\n    }\n}\n", [])
arm("A2 nested closures + nested mods inside #[cfg(test)] are PERMITTED",
    "#[cfg(test)]\nmod tests {\n    fn a() { let f = || fold_bytes32_to_bb(&y); }\n"
    "    mod deeper {\n        fn b() { let z = fold_value32(&y); }\n    }\n}\n", [])
arm("A3 zero-initialisers are PERMITTED (scratch buffers, not commitments)",
    "fn p() -> [B;8] {\n    let a = [0; 8];\n    let b = [B::ZERO; 8];\n    b\n}\n", [])
arm("A4 the FAITHFUL 8-felt encoding is PERMITTED",
    "fn p(x: &[u8;32]) -> [B;8] {\n    bytes32_to_8_limbs(x)\n}\n", [])

# ── BOTH POLES IN ONE FILE: production refused while its own test exhibit passes ─
arm("B1 one file, production REFUSED and its cfg(test) exhibit PERMITTED",
    "fn accumulator_leaf(x: &[u8;32]) -> B {\n    fold_bytes32_to_bb(x)\n}\n\n"
    "#[cfg(test)]\nmod tests {\n    fn t() { let legacy = fold_bytes32_to_bb(&y); }\n}\n", [2])

width = max(len(n) for n, *_ in results)
allok = True
for name, ok, got, exp in results:
    allok &= ok
    detail = "" if ok else f"   <-- flagged {got}, expected {exp}"
    print(f"[{'PASS' if ok else 'BROKEN'}] {name:<{width}}{detail}")
print()
print("=" * 78)
print(f"VERDICT: {'all arms behaved' if allok else 'SOME ARMS MISBEHAVED'}  ({len(results)} arms)")
print("=" * 78)
sys.exit(0 if allok else 1)
