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
    scripts/measure-descriptor-normal-form.py --fold-file <f>  # print <f> constant-folded
    scripts/measure-descriptor-normal-form.py --fold           # what the FOLD costs this corpus
    scripts/measure-descriptor-normal-form.py --compare A B    # ⚑ THE COMPARATOR

## ⚑ The comparator, and what licenses it

`--compare A B` classifies every arithmetic body as IDENTICAL / COSMETIC / SEMANTIC by
canonicalizing both sides before diffing. That is sound by a theorem already on disk —
`AirNormalForm.canonicalize_eval` proves `(canonicalize e).eval a = e.eval a` for EVERY assignment,
so two bodies with the same canonical form denote the same polynomial. It costs zero bytes, zero
VK rotations and zero re-emissions: nothing is installed, the artifact is not touched.

⚠ **Only one direction is a theorem.** COSMETIC means "proved to mean the same". SEMANTIC means
"these did not reduce to one head" — look at it — and NEVER "the polynomials differ".

⚠ **The comparator does not normalize a lookup / memOp / mapOp / umemOp / proofBind tuple.** Those
are compared as raw bytes, because the chip bus is keyed on the bare tuple shape and there is no
`canonicalize_eval` for them. A tuple byte change is reported as a SHAPE change, never as cosmetic.

## ⚠ Two different passes live here; do not read one as a phase of the other

`--canon` is `gCanon`: it reaches the normal form and GROWS the corpus. `--fold` / `--fold-file` is
`gFold`: it deletes every `mul(const, const)` and buys **exactly zero** normality. `GateExpr` §6c
carries both columns.
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
# The FOLD (the Lean `GateExpr.gFold`, in Python) — the OTHER axis of the pass
# table in `GateExpr` §6c. It deletes every `mul(const, const)` subtree and buys
# EXACTLY ZERO normality; `canonicalize` buys all the normality and grows the
# corpus. Neither is the other's phase.
# ─────────────────────────────────────────────────────────────────────────────
def fold_const(e: dict) -> dict:
    """`Dregg2.Circuit.GateExpr.gFold`, four cases, verbatim."""
    t = e["t"]
    if t in LEAVES or t == "const":
        return e
    a, b = fold_const(e["l"]), fold_const(e["r"])
    if a["t"] == "const" and b["t"] == "const":
        return {"t": "const", "v": a["v"] + b["v"] if t == "add" else a["v"] * b["v"]}
    return {"t": t, "l": a, "r": b}


def node_count(e: dict) -> int:
    if e["t"] in LEAVES or e["t"] == "const":
        return 1
    return 1 + node_count(e["l"]) + node_count(e["r"])


def dead_products(e: dict) -> int:
    """`mul(const, const)` subtrees — what the fold deletes."""
    if e["t"] in LEAVES or e["t"] == "const":
        return 0
    n = dead_products(e["l"]) + dead_products(e["r"])
    if e["t"] == "mul" and e["l"]["t"] == "const" and e["r"]["t"] == "const":
        n += 1
    return n


# ─────────────────────────────────────────────────────────────────────────────
# ⚑ THE COMPARATOR. Two bodies MEAN THE SAME THING iff they canonicalize to the
# same head — and that is SOUND BY A LANDED THEOREM, not by inspection:
# `AirNormalForm.canonicalize_eval` says `(canonicalize e).eval a = e.eval a` for
# every assignment, so equal canonical forms imply equal polynomials.
#
# ⚠ THE DIRECTION THAT HOLDS IS THE ONE USED. Equal canonical form ⇒ equal
# denotation (that is the theorem). The converse is NOT claimed: two bodies can
# denote the same polynomial and differ canonically only if the head vocabulary
# distinguishes them, so a `SEMANTIC DRIFT` verdict is "these did not reduce to
# one head", never a proof that the polynomials differ. Read it as: SAME = proved
# same meaning; DIFFERENT = not proved same, look.
# ─────────────────────────────────────────────────────────────────────────────
def same_meaning(a: dict, b: dict) -> bool:
    """Sound by `canonicalize_eval`: equal canonical form ⇒ equal polynomial."""
    return canonicalize(a) == canonicalize(b)


def classify_body(a: dict, b: dict) -> str:
    """IDENTICAL / COSMETIC (same meaning, different bytes) / SEMANTIC."""
    if a == b:
        return "identical"
    return "cosmetic" if same_meaning(a, b) else "semantic"


def compare_descriptors(old: dict, new: dict) -> dict:
    """Diff two descriptor JSONs body-by-body through the comparator.

    Returns counts plus the per-constraint verdicts that are not `identical`.
    A SHAPE change (name/width/pi/table/constraint-count) is reported separately
    and is never laundered into `cosmetic`.
    """
    shape = []
    for k in ("name", "trace_width", "public_input_count", "challenges", "tables"):
        if old.get(k) != new.get(k):
            shape.append(f"{k}: {old.get(k)!r} -> {new.get(k)!r}")
    oc, nc = old.get("constraints", []), new.get("constraints", [])
    if len(oc) != len(nc):
        shape.append(f"constraint count: {len(oc)} -> {len(nc)}")
        return {"shape": shape, "identical": 0, "cosmetic": 0, "semantic": 0, "detail": []}

    counts = {"identical": 0, "cosmetic": 0, "semantic": 0}
    detail, nodes_old, nodes_new = [], 0, 0
    for i, (o, n) in enumerate(zip(oc, nc)):
        if o.get("t") != n.get("t"):
            shape.append(f"constraint {i}: kind {o.get('t')} -> {n.get('t')}")
            continue
        if o.get("t") not in ("gate", "boundary", "window_gate"):
            # Non-arithmetic (lookup / memOp / mapOp / umemOp / proofBind) tuples
            # are compared as RAW BYTES — the chip bus is keyed on the bare tuple
            # shape, so the comparator has no licence to normalize there.
            if o != n:
                shape.append(f"constraint {i} ({o.get('t')}): tuple bytes differ")
            continue
        v = classify_body(o["body"], n["body"])
        counts[v] += 1
        nodes_old += node_count(o["body"])
        nodes_new += node_count(n["body"])
        if v != "identical":
            detail.append((i, o.get("t"), v))
    counts["shape"] = shape
    counts["detail"] = detail
    counts["nodes_old"] = nodes_old
    counts["nodes_new"] = nodes_new
    return counts


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
    ap.add_argument("--fold-file", metavar="FILE", help="print FILE with every body const-folded")
    ap.add_argument(
        "--fold", action="store_true", help="what the FOLD would do to this corpus (not normality)"
    )
    ap.add_argument(
        "--compare",
        nargs=2,
        metavar=("OLD", "NEW"),
        help="the COMPARATOR: diff two descriptor JSONs through canonicalization "
        "(sound by AirNormalForm.canonicalize_eval). Exit 1 on a semantic or shape change.",
    )
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

    if args.fold_file:
        d = json.load(open(args.fold_file))
        for c in d["constraints"]:
            if c["t"] in ("gate", "boundary", "window_gate"):
                c["body"] = fold_const(c["body"])
        print(json.dumps(d, separators=(",", ":")))
        return 0

    if args.compare:
        old_p, new_p = args.compare
        r = compare_descriptors(json.load(open(old_p)), json.load(open(new_p)))
        print(f"comparator:          {os.path.basename(old_p)} -> {os.path.basename(new_p)}")
        print(f"  identical bodies:  {r['identical']}")
        print(f"  COSMETIC bodies:   {r['cosmetic']}   (same polynomial, different bytes)")
        print(f"  SEMANTIC bodies:   {r['semantic']}   (did NOT reduce to one head)")
        if "nodes_old" in r:
            d = r["nodes_new"] - r["nodes_old"]
            print(f"  AST nodes:         {r['nodes_old']:,} -> {r['nodes_new']:,} ({d:+,})")
        for line in r["shape"]:
            print(f"  SHAPE CHANGE:      {line}")
        for i, kind, v in r["detail"][:40]:
            print(f"      constraint {i:5d} ({kind}): {v.upper()}")
        if r["shape"] or r["semantic"]:
            print("VERDICT: NOT a pure re-encoding — a shape or unproved-equal body moved.")
            return 1
        if r["cosmetic"]:
            print("VERDICT: COSMETIC — every body proves equal under canonicalize_eval.")
        else:
            print("VERDICT: BYTE-IDENTICAL.")
        return 0

    if args.fold:
        files = sorted(glob.glob(os.path.join(args.dir, "*.json")))
        if not files:
            print(f"no descriptors under {args.dir}", file=sys.stderr)
            return 2
        n_before = n_after = dead = 0
        norm_before = norm_after = 0
        moving = []
        for f in files:
            d = json.load(open(f))
            b = a = dd = 0
            bad_b = bad_a = False
            for _, body in bodies(d, False):
                fb = fold_const(body)
                b += node_count(body)
                a += node_count(fb)
                dd += dead_products(body)
                nb, na = is_normal(body), is_normal(fb)
                norm_before += nb
                norm_after += na
                bad_b = bad_b or not nb
                bad_a = bad_a or not na
            n_before += b
            n_after += a
            dead += dd
            if a != b:
                moving.append((os.path.basename(f), a - b, dd))
        print(f"descriptors:         {len(files)}")
        print(f"AST nodes:           {n_before:,} -> {n_after:,}  ({n_after - n_before:+,})")
        print(f"descriptors MOVING:  {len(moving)} / {len(files)}   (every one SHRINKS)")
        print(f"dead mul(const,const): {dead:,} -> 0")
        print(f"bodies NORMAL:       {norm_before:,} -> {norm_after:,}   <- ⚠ the fold buys ZERO")
        print("\nPER-DESCRIPTOR node delta (a total hides the shape):")
        for n, dl, dd in sorted(moving, key=lambda r: r[1]):
            print(f"    {dl:+8,d}  dead={dd:<6d} {n}")
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
