#!/usr/bin/env python3
"""measure-descriptor-normal-form.py — the BYTE-REACHABILITY measurement, re-derivable.

`metatheory/docs/LOGIC-COMPILER-ASSESSMENT.md` §P2.5 reports a byte-reachability number over the
76 checked-in `circuit/descriptors/by-name/*.json`. Phase 2 measured it with a script nobody
committed, so the number could not be re-derived and Phase 3 could not confirm it moved. This is
that script, committed, so `N/76` is a command rather than a claim.

## What it measures

A descriptor is BYTE-REACHABLE iff every arithmetic body it carries is in the CANONICAL NORMAL
FORM — the shape `Dregg2/Circuit/Emit/AirNormalForm.lean` fixes as the corpus invariant and
`AirBuilder.headToExpr` produces:

    body ::= atom | add(body, atom)          -- LEFT-nested spine
    atom ::= mul(const c, prod) | const k    -- EVERY term carries its coefficient, INCLUDING c = 1
    prod ::= leaf | mul(prod, leaf)          -- LEFT-nested; leaf = var / loc / nxt

Bodies checked: `gate`, `boundary`, `window_gate`. Lookup tuples are deliberately NOT checked —
they are not polynomials asserted to vanish, and the chip bus is keyed on the bare tuple shape
(see `AirNormalForm`'s header).

⚠ The `--strict-gates` mode reproduces Phase 2's narrower question ("every GATE body in builder
normal form"), which ignores boundary and window bodies; it is kept so the two eras' numbers are
comparable. The default is the whole invariant.

## Usage

    scripts/measure-descriptor-normal-form.py                  # the readout
    scripts/measure-descriptor-normal-form.py --list           # + per-descriptor verdicts
    scripts/measure-descriptor-normal-form.py --strict-gates   # Phase 2's gate-only question
    scripts/measure-descriptor-normal-form.py --canon <file>   # print <file> canonicalized
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import sys

LEAVES = ("var", "loc", "nxt")


# ─────────────────────────────────────────────────────────────────────────────
# The shape predicate (the Lean `AirNormalForm.isNormal` / `isNormalW`, in Python).
# ─────────────────────────────────────────────────────────────────────────────
def is_leaf(e: dict) -> bool:
    return e["t"] in LEAVES


def is_var_prod(e: dict) -> bool:
    if is_leaf(e):
        return True
    if e["t"] == "mul":
        return is_var_prod(e["l"]) and is_leaf(e["r"])
    return False


def is_term_atom(e: dict) -> bool:
    if e["t"] == "const":
        return True
    if e["t"] == "mul":
        return e["l"]["t"] == "const" and is_var_prod(e["r"])
    return False


def spine(e: dict) -> list[dict]:
    if e["t"] == "add":
        return spine(e["l"]) + [e["r"]]
    return [e]


def is_normal(e: dict) -> bool:
    return all(is_term_atom(a) for a in spine(e))


# ─────────────────────────────────────────────────────────────────────────────
# The normalizer (the Lean `exprToHead` + `headToExpr`, in Python) — so this script
# can PREVIEW the bytes a re-emission produces without a multi-hour Lean build.
# A term is (coeff, [leaf, ...]); a head is (terms, const).
# ─────────────────────────────────────────────────────────────────────────────
def _leaf_key(e: dict):
    return (e["t"], e["c"] if "c" in e else e["v"])


def _leaf_json(k) -> dict:
    tag, idx = k
    return {"t": tag, "c": idx} if tag in ("loc", "nxt") else {"t": tag, "v": idx}


def expr_to_head(e: dict):
    """`Dregg2.Circuit.Emit.EffectLower.exprToHead`, verbatim (guarded `mulHead`)."""
    t = e["t"]
    if t in LEAVES:
        return ([(1, [_leaf_key(e)])], 0)
    if t == "const":
        return ([], e["v"])
    if t == "add":
        lt, lc = expr_to_head(e["l"])
        rt, rc = expr_to_head(e["r"])
        return (lt + rt, lc + rc)
    if t == "mul":
        ht, hc = expr_to_head(e["l"])
        ot, oc = expr_to_head(e["r"])
        terms = [(a * b, ac + bc) for (a, ac) in ht for (b, bc) in ot]
        # ⚑ the constant cross-products are GUARDED on a nonzero constant, exactly as
        # `mulHead` is: multiplying by a zero constant contributes no term.
        if oc != 0:
            terms += [(a * oc, ac) for (a, ac) in ht]
        if hc != 0:
            terms += [(hc * b, bc) for (b, bc) in ot]
        return (terms, hc * oc)
    raise ValueError(f"unknown expression tag {t!r}")


def vars_prod(cols) -> dict:
    acc = _leaf_json(cols[0])
    for c in cols[1:]:
        acc = {"t": "mul", "l": acc, "r": _leaf_json(c)}
    return acc


def term_to_expr(term) -> dict:
    coeff, cols = term
    if not cols:
        return {"t": "const", "v": coeff}
    return {"t": "mul", "l": {"t": "const", "v": coeff}, "r": vars_prod(cols)}


def head_to_expr(head) -> dict:
    terms, const = head
    es = [term_to_expr(t) for t in terms]
    if const != 0:
        es.append({"t": "const", "v": const})
    if not es:
        return {"t": "const", "v": 0}
    acc = es[0]
    for e in es[1:]:
        acc = {"t": "add", "l": acc, "r": e}
    return acc


def canonicalize(e: dict) -> dict:
    return head_to_expr(expr_to_head(e))


# ─────────────────────────────────────────────────────────────────────────────
def bodies(desc: dict, strict_gates: bool):
    for c in desc["constraints"]:
        if c["t"] == "gate":
            yield "gate", c["body"]
        elif not strict_gates and c["t"] in ("boundary", "window_gate"):
            yield c["t"], c["body"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true", help="per-descriptor verdicts")
    ap.add_argument("--strict-gates", action="store_true", help="Phase 2's gate-only question")
    ap.add_argument("--canon", metavar="FILE", help="print FILE with every body canonicalized")
    ap.add_argument(
        "--dir",
        default=os.path.join(
            os.path.dirname(os.path.abspath(__file__)), "..", "circuit", "descriptors", "by-name"
        ),
    )
    args = ap.parse_args()

    if args.canon:
        d = json.load(open(args.canon))
        for c in d["constraints"]:
            if c["t"] in ("gate", "boundary", "window_gate"):
                c["body"] = canonicalize(c["body"])
        print(json.dumps(d, separators=(",", ":")))
        return 0

    files = sorted(glob.glob(os.path.join(args.dir, "*.json")))
    if not files:
        print(f"no descriptors under {args.dir}", file=sys.stderr)
        return 2

    ok, tot_bodies, bad_bodies = [], 0, 0
    rows = []
    for f in files:
        d = json.load(open(f))
        bs = list(bodies(d, args.strict_gates))
        bad = [b for _, b in bs if not is_normal(b)]
        tot_bodies += len(bs)
        bad_bodies += len(bad)
        rows.append((os.path.basename(f), len(bad), len(bs)))
        if not bad:
            ok.append(os.path.basename(f))

    mode = "GATE bodies only (Phase 2's question)" if args.strict_gates else "ALL arithmetic bodies"
    print(f"method:              {mode}")
    print(f"descriptors:         {len(files)}")
    print(f"BYTE-REACHABLE:      {len(ok)} / {len(files)}")
    print(f"bodies:              {tot_bodies}")
    print(f"bodies NOT canonical:{bad_bodies:>7}")
    if args.list:
        print("\nCANONICAL:")
        for n in ok:
            print(f"    {n}")
        print("\nNON-CANONICAL (bad/total):")
        for n, b, t in sorted(rows, key=lambda r: -r[1]):
            if b:
                print(f"    {b:6d}/{t:<6d} {n}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
