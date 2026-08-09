#!/usr/bin/env python3
"""Refuse an `@[implemented_by]` that sits on the def a differential would compare against.

⚑ THE MECHANISM THIS EXISTS FOR (measured 2026-08-09, `docs/reference/PROOF-STRATEGY-2026-08-09.md`
§2.2). `@[implemented_by]` is honoured by the COMPILED evaluator, and `#guard` / `native_decide` /
`#eval` all run on that evaluator. So when the attribute is attached to the PURE def, the obvious
differential is a TAUTOLOGY:

    def pureF (n : Nat) : Nat := n + 1
    def twinF (n : Nat) : Nat := n + 999
    attribute [implemented_by twinF] pureF
    #eval pureF 1                    -- 1000, the TWIN answers
    #eval (twinF 1 == pureF 1)       -- true, for ANY twin, always
    theorem k : pureF 1 = 2 := rfl   -- and the kernel still sees the pure body

The seam is then not merely untested but UNTESTABLE, and a contributor who "closes the gap" gets a
permanently green check that reads as closure. That is worse than no check. Five ML-DSA ring seams
sat in exactly this shape on the live FIPS 204 sign/verify path until 2026-08-09; the sixth
(`BlocklaceFinality.tauOrderFast`) escaped only because its attribute happened to be on an ALIAS,
which is why it is the one seam in the tree that had a real differential.

THE RULE. Every `@[implemented_by]` target must be an ALIAS carrying a same-file witness theorem
`<target>_eq` that says which pure def it denotes, and no def named by such a witness may itself be
a routed target. That is the structural property, not a naming convention: it forces the existence
of an unrouted pure side for a differential to compare against.

Usage:
    check-implemented-by-alias.py            # scan the working tree
    check-implemented-by-alias.py --self-test  # red-proof: the checker must REJECT a planted seam
"""
from __future__ import annotations

import argparse
import os
import re
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOTS = ["metatheory", "orb", "orb-compiler", "tools", "fhegg-rtl", "dregg-serve-spec"]
ALLOW = os.path.join(REPO, "scripts", "implemented-by-alias-allow.txt")

IDENT = r"[A-Za-z_][A-Za-z0-9_'!?.«»]*"


def strip_comments(src: str) -> str:
    """Blank out Lean block comments (nesting-aware, `/-` and `/--`) and `--` line comments.

    Prose mentions of `@[implemented_by]` are the overwhelming majority of matches in this repo
    (55 of 61 at the time of writing), so a checker that reads comments reports nothing but noise.
    Newlines are preserved so line numbers stay true.
    """
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        two = src[i : i + 2]
        if depth == 0 and two == "/-":
            depth, i = 1, i + 2
            out.append("  ")
            continue
        if depth > 0:
            if two == "/-":
                depth, i = depth + 1, i + 2
                out.append("  ")
                continue
            if two == "-/":
                depth, i = depth - 1, i + 2
                out.append("  ")
                continue
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        if two == "--":
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


ATTR_LINE = re.compile(r"attribute\s*\[([^\]]*)\]\s*(.*)")
INLINE_ATTR = re.compile(r"@\[([^\]]*)\]")
DECL_HEAD = re.compile(r"\b(?:def|abbrev|opaque|partial\s+def|unsafe\s+def)\s+(" + IDENT + r")")


def routed_targets(text: str):
    """Every declaration name this file routes through `@[implemented_by]`, with its line."""
    found = []
    lines = text.split("\n")
    for idx, line in enumerate(lines, start=1):
        m = ATTR_LINE.search(line)
        if m and "implemented_by" in m.group(1):
            for t in re.findall(IDENT, m.group(2)):
                found.append((t, idx))
            continue
        for am in INLINE_ATTR.finditer(line):
            if "implemented_by" not in am.group(1):
                continue
            # the decl this attribute decorates: same line after `]`, else the following lines
            tail = line[am.end() :]
            dm = DECL_HEAD.search(tail)
            look = 0
            while dm is None and idx + look < len(lines) and look < 6:
                dm = DECL_HEAD.search(lines[idx + look])
                look += 1
            if dm:
                found.append((dm.group(1), idx))
    return found


def witness_rhs(text: str, target: str):
    """The RHS identifiers of the alias witness `theorem <target>_eq …`, or None if absent."""
    m = re.search(
        r"\b(?:theorem|lemma)\s+" + re.escape(target) + r"_eq\b(.*?)(?::=|\bby\b)",
        text,
        re.S,
    )
    if not m:
        return None
    stmt = m.group(1)
    eq = stmt.find("=")
    if eq < 0:
        return []
    return re.findall(IDENT, stmt[eq + 1 :])


def load_allow():
    allowed = set()
    if not os.path.exists(ALLOW):
        return allowed
    for raw in open(ALLOW):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key = line.split("#")[0].strip()
        if key:
            allowed.add(key)
    return allowed


def scan(root_dir: str, roots=None, allow=None):
    allow = allow if allow is not None else set()
    failures = []
    checked = 0
    for root in roots if roots is not None else ROOTS:
        base = os.path.join(root_dir, root)
        if not os.path.isdir(base):
            continue
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = [d for d in dirnames if d != ".lake"]
            for fn in sorted(filenames):
                if not fn.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, fn)
                rel = os.path.relpath(path, root_dir)
                text = strip_comments(open(path, encoding="utf-8", errors="replace").read())
                targets = routed_targets(text)
                if not targets:
                    continue
                names = {t for t, _ in targets}
                for target, line in targets:
                    key = f"{rel}::{target}"
                    if key in allow:
                        continue
                    checked += 1
                    rhs = witness_rhs(text, target)
                    if rhs is None:
                        failures.append(
                            f"{rel}:{line}: `@[implemented_by]` on `{target}` with NO alias "
                            f"witness. Add `theorem {target}_eq : {target} = <the pure def> := rfl` "
                            f"in this file — without an unrouted pure side, the differential for "
                            f"this seam is a tautology and cannot go red."
                        )
                        continue
                    pure = [r for r in rhs if r not in names]
                    if not pure:
                        failures.append(
                            f"{rel}:{line}: `{target}_eq` names only ROUTED constants "
                            f"({', '.join(rhs) or 'nothing'}) — every side of the witness carries "
                            f"an `@[implemented_by]`, so a differential built on it compares the "
                            f"twin with itself."
                        )
    return checked, failures


SELF_TEST_OK = """
namespace T
def pureF (n : Nat) : Nat := n + 1
def twinF (n : Nat) : Nat := n + 999
def pureFFast (n : Nat) : Nat := pureF n
theorem pureFFast_eq : pureFFast = pureF := rfl
attribute [implemented_by twinF] pureFFast
end T
"""

SELF_TEST_BAD_NO_WITNESS = """
namespace T
def pureF (n : Nat) : Nat := n + 1
def twinF (n : Nat) : Nat := n + 999
attribute [implemented_by twinF] pureF
end T
"""

SELF_TEST_BAD_INLINE = """
namespace T
def twinG (n : Nat) : Nat := n + 999
@[implemented_by twinG]
def pureG (n : Nat) : Nat := n + 1
end T
"""

SELF_TEST_BAD_ROUTED_RHS = """
namespace T
def a (n : Nat) : Nat := n + 1
def b (n : Nat) : Nat := a n
def tw (n : Nat) : Nat := n
theorem b_eq : b = a := rfl
attribute [implemented_by tw] b
attribute [implemented_by tw] a
end T
"""

SELF_TEST_PROSE_ONLY = """
/-- This docstring talks about `@[implemented_by]` a lot and even shows
    `attribute [implemented_by twinF] pureF` in an example block. -/
def harmless : Nat := 1
-- attribute [implemented_by twinF] pureF
"""


def self_test() -> int:
    cases = [
        ("compliant alias", SELF_TEST_OK, False),
        ("attribute on the pure def, no witness", SELF_TEST_BAD_NO_WITNESS, True),
        ("inline @[implemented_by] on the pure def", SELF_TEST_BAD_INLINE, True),
        ("witness whose RHS is itself routed", SELF_TEST_BAD_ROUTED_RHS, True),
        ("prose/comment mention only", SELF_TEST_PROSE_ONLY, False),
    ]
    bad = 0
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "metatheory"))
        for name, body, want_red in cases:
            path = os.path.join(td, "metatheory", "Case.lean")
            open(path, "w").write(body)
            checked, failures = scan(td, roots=["metatheory"], allow=set())
            got_red = bool(failures)
            ok = got_red == want_red
            print(
                f"  [{'ok ' if ok else 'FAIL'}] {name}: "
                f"{'RED' if got_red else 'green'} (wanted {'RED' if want_red else 'green'})"
                + (f" — {failures[0]}" if failures else "")
            )
            if not ok:
                bad += 1
    if bad:
        print(f"SELF-TEST FAILED: {bad} case(s) — this checker cannot be trusted.")
        return 1
    print("SELF-TEST PASSED: the checker reds on a planted seam and stays green on a compliant one.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--self-test", action="store_true", help="red-proof the checker itself")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    checked, failures = scan(REPO, allow=load_allow())
    if failures:
        print("implemented-by-alias FAIL — a routed def with no unrouted pure side:")
        for f in failures:
            print("  " + f)
        print(
            "\nThe fix is the alias, not the allow-list: introduce `<name>Fast` as a `rfl`-alias, "
            "move the attribute onto it, retarget the executable callers, and leave the pure def "
            "unrouted so a differential can observe both sides."
        )
        return 1
    print(f"implemented-by-alias OK: {checked} routed target(s), each with an unrouted pure side.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
