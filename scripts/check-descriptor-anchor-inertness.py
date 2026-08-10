#!/usr/bin/env python3
"""check-descriptor-anchor-inertness.py — a served descriptor's DECORATIVE PUBLIC INPUTS may only ratchet DOWN.

═══ THE CLASS THIS GATE EXISTS TO CATCH ═══════════════════════════════════════════
A `pi_binding` ties a trace column to a public input. It ties it to NOTHING ELSE. So a
descriptor can publish a block hash, a slot, a state root — and never mention that column
in a single gate body or lookup tuple. A verifying proof then says "the prover exhibited
these numbers", and the reader, seeing them in the public inputs of a proof that also
checks a quorum, believes the quorum was ABOUT them.

Found by hand three times in this repo before this gate existed:
  * Solana  (`LightClientSolanaAir.lean` §6b, 2026-08-03) — eleven anchors, zero gates.
  * Midnight / Tendermint — noted in the SAME docblock as "the identical decomposition
    holds", in PROSE, which is not a gate (`feedback-a-documented-wound-is-not-a-detected-one`).
  * Ethereum / Mina-verify — 2026-08-04, this sweep.

⚑ THE MEASUREMENT IS NOT A JUDGEMENT. Build the column-connectivity graph of the emitted
object — two columns adjacent iff they CO-OCCUR in one constraint that relates them (a gate
body, a boundary body, a window-gate body, a lookup tuple, a hash site, a transition pair,
a mem/map/proof bus op) — and read off the connected components. A PI-bound column whose
component is a SINGLETON is related to nothing in the circuit: decorative.

`loc c` and `nxt c` are the SAME column: a window gate relating `loc 9` to `nxt 0` is a real
edge 9—0, which is exactly how `dregg-mina-lightclient-link::v1` earns its zero.

⚠ TWO SEPARATE FACTS, KEPT SEPARATE — the finer one is the one that matters.
  * UNREAD   — the column appears in no constraint's column list at all.
  * DECORATIVE — the column appears in no constraint that relates it to another column.
    An ARITY-1 RANGE LOOKUP reads a column and relates it to nothing; it bounds a shape, it
    does not tie the value to the evidence. `dregg-mina-lightclient-verify::v1`'s eighteen
    state limbs are READ (29/22-bit lane bounds) and DECORATIVE. Counting them as bound
    because a range table touches them is precisely the laundering this gate refuses.

═══ WHY A RATCHET AND NOT A BAN ═══════════════════════════════════════════════════
Sixty-three decorative anchors are live across the served set today and several are honest
(a nonce, a domain tag). A flat ban is a gate nobody can keep green, which is the same as no
gate. So: a PER-DESCRIPTOR baseline in `scripts/descriptor-anchor-inertness-baseline.txt`
that may only SHRINK. Three red paths:

  (a) ABOVE baseline — a descriptor gained a decorative anchor. This is the bleed.
  (b) BELOW baseline — a STALE ROW. You bound an anchor and did not retire the number;
      retiring is forced, which makes the census monotone rather than merely non-increasing.
  (c) UNLISTED and carrying decorative anchors — a NEW descriptor served with them.

⚠ WHAT A GREEN HERE DOES NOT MEAN — read before trusting it:
  * NOT that a connected anchor is SOUND. Connectivity is co-occurrence, not derivation.
    `dregg-mina-lightclient-link::v1` chains nine witnessed lanes by equality and never
    hashes anything; every PI is connected and every `OWNHASH` is still a free witness.
    This gate cannot see the difference between "derived" and "equal to another witness".
  * NOT that the anchors are related to EACH OTHER usefully. A two-column island is a
    component; so is the whole circuit.
  * NOTHING about carrier bits forced `= 1`. A one-column gate pinning `ED_OK = 1` leaves
    `ED_OK` a singleton and it is not PI-bound, so it never appears here. `--carriers`
    prints them; no baseline constrains them.
  * NOTHING about which VALUE a column may take, only about what it is joined to.

Usage:
  scripts/check-descriptor-anchor-inertness.py            # gate (reads the baseline)
  scripts/check-descriptor-anchor-inertness.py --report   # full decomposition, all descriptors
  scripts/check-descriptor-anchor-inertness.py --report --only lightclient
  scripts/check-descriptor-anchor-inertness.py --carriers # + single-column gate columns
  scripts/check-descriptor-anchor-inertness.py --write-baseline
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
DESC_DIR = REPO / "circuit" / "descriptors" / "by-name"
BASELINE = REPO / "scripts" / "descriptor-anchor-inertness-baseline.txt"

# ── SCOPE ─ this pair is the ONLY copy; it prints on every run, pass or fail. ─────────
SCOPE_ANSWERS = (
    "for every `ir == 2` descriptor JSON under circuit/descriptors/by-name/, does its count "
    "of DECORATIVE public inputs — `pi_binding` columns that are a SINGLETON in the "
    "co-occurrence graph over gate/boundary/window-gate bodies, arity>1 lookup tuples, hash "
    "sites, transitions and mem/map/umem/proof_bind operands, with an arity-1 range lookup "
    "counted as a READ that joins the column to nothing — exactly equal its row in "
    "scripts/descriptor-anchor-inertness-baseline.txt?"
)
SCOPE_DOES_NOT_ANSWER = (
    "whether an anchor BINDS anything. This is a ratchet over a recorded number: green means "
    "no by-name descriptor gained a decorative anchor and none silently lost one, NOT that the "
    "baselined anchors are load-bearing. Co-occurrence is not derivation — a chain of witnessed "
    "lanes joined by equality scores zero — and any descriptor outside by-name/ (the rotation "
    "registry TSVs, table-airs/, the top-level descriptors) is never opened."
)
SCOPE_ANSWERS_SELFTEST = (
    "do five synthetic four-column descriptors get the decorative verdicts they were built to "
    "have (pinned-and-never-named, read-by-an-arity-1-range-lookup-only, joined-by-a-window-gate, "
    "joined-by-a-chal_gate, and joined-by-nothing-but-a-shared-challenge), and does a count above "
    "a baseline row get collected as red?"
)
SCOPE_DOES_NOT_ANSWER_SELFTEST = (
    "anything about the descriptors on disk, and nothing about main()'s ratchet either: the "
    "fourth case re-implements the baseline comparison in three lines rather than calling "
    "main() or read_baseline(), so a broken comparison THERE stays invisible here."
)

# `var v` is a row-local column; `loc c` / `nxt c` are the SAME column read in two rows.
EXPR_COL_KEY = {"var": "v", "loc": "c", "nxt": "c"}

# ⚑ `chal i` is a VERIFIER-DRAWN SCALAR, not a trace column. It carries no column index and
# must contribute none: a Schwartz–Zippel body `α·(a - b) + α²·(c - d)` relates a,b,c,d to each
# other and relates NOTHING to `α`. Listed here rather than falling through to the `else` so the
# omission is a decision with a reason, not a tag the walker happened not to meet.
EXPR_SCALAR_LEAVES = ("const", "chal")


def expr_cols(e, out):
    t = e["t"]
    if t in EXPR_COL_KEY:
        out.add(e[EXPR_COL_KEY[t]])
    elif t in EXPR_SCALAR_LEAVES:
        pass
    elif t in ("add", "mul"):
        expr_cols(e["l"], out)
        expr_cols(e["r"], out)
    else:
        raise ValueError(f"unknown expr tag {t!r} — the IR grew a node this gate cannot read")
    return out


class DSU:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb


def analyze(d: dict) -> dict:
    """The column-connectivity decomposition of one IR-v2 descriptor."""
    width = d["trace_width"]
    dsu = DSU(width)
    pi: dict[int, list] = {}
    read = collections.Counter()          # appears in SOME constraint's column list
    related = collections.Counter()       # appears in a constraint relating it to another column
    unary_gate: dict[int, list] = {}      # a gate/window body touching exactly ONE column
    reads_by: dict[int, list] = collections.defaultdict(list)   # col -> [(kind, idx), ...]
    range_bits: dict[int, list] = collections.defaultdict(list)
    tables = {t["id"]: t for t in d.get("tables", [])}

    def relate(cols: set[int], kind: str, idx: int):
        cols = sorted(cols)
        for c in cols:
            read[c] += 1
            reads_by[c].append((kind, idx))
        if len(cols) == 1:
            unary_gate.setdefault(cols[0], []).append((kind, idx))
            return
        for c in cols[1:]:
            dsu.union(cols[0], c)
        for c in cols:
            related[c] += 1

    for i, c in enumerate(d["constraints"]):
        t = c["t"]
        if t == "gate":
            relate(expr_cols(c["body"], set()), "gate", i)
        elif t == "boundary":
            relate(expr_cols(c["body"], set()), "boundary:" + c["row"], i)
        elif t == "window_gate":
            relate(expr_cols(c["body"], set()),
                   "window_gate@" + ("transition" if c["on_transition"] else "all"), i)
        elif t == "chal_gate":
            # ⚑ THE CHALLENGE GATE (Lean `ChalConstraint.toJson`, Rust `VmConstraint2::ChalGate`).
            # Same two-row `loc`/`nxt` body as `window_gate`, plus the `chal i` leaf. It is a
            # polynomial identity the verifier checks at random coefficients, so the columns in
            # one body are related exactly as strongly as in a plain gate — this is how the
            # `pasta-*-sz` descriptors tie their operand lanes to their result lanes, and reading
            # it as anything weaker would score those anchors decorative when they are not.
            relate(expr_cols(c["body"], set()),
                   "chal_gate@" + ("transition" if c["on_transition"] else "all"), i)
        elif t == "lookup":
            cols = set()
            for e in c["tuple"]:
                expr_cols(e, cols)
            tb = tables.get(c["table"], {})
            name = tb.get("name", f"tid{c['table']}")
            if tb.get("sem") == "range" and len(c["tuple"]) == 1:
                for cc in cols:
                    range_bits[cc].append(tb.get("bits"))
                    read[cc] += 1          # READ, and deliberately NOT related
                    reads_by[cc].append((f"range:{name}/{tb.get('bits')}b", i))
                continue
            relate(cols, f"lookup:{name}", i)
        elif t == "pi_binding":
            pi.setdefault(c["col"], []).append((c["pi_index"], c["row"]))
        elif t == "transition":
            relate({c["hi"], c["lo"]}, "transition", i)
        elif t == "proof_bind":
            # ⚑⚑ EMISSION-FAITHFUL, one relate() per EMITTED POLYNOMIAL (fixed 2026-08-08; the
            # 2026-08-05 fix below this arm made the lane SEQUENCES visible, and then over-read
            # them). `descriptor_ir2.rs`'s `ProofBind` arm emits:
            #
            #     guard*(guard - 1)                     always     -- the guard's columns only
            #     guard*(vk_i - vk_pin_i)   per lane,   iff vk_pin -- guard  U  vk_i
            #     guard*(commit_i - bound_i) per lane,  iff bound  -- guard  U  commit_i  U  bound_i
            #
            # A `bound := none` seam emits NOTHING over its `commit` lanes, so a walker that
            # related the whole declaration scored columns that appear in no emitted constraint as
            # joined — and its 18 -> 9 was quoted as gate coverage. Measured the hour THIS fix
            # landed: `dregg-mina-lightclient-verify::v1` 9 -> 36 decorative anchors (the tip and
            # both sub-proof-commitment nonets return), `dregg-mina-lightclient-link::v1` 0 -> 17
            # (the body flag-day columns), no descriptor byte having moved. The Lean twin is
            # `LightClientAnchorConnectivity.relatedCols`' `.proofBind` arm, same day; the
            # DECLARATION reading lives there as `declaredCols`, under a name that says so.
            # `vk_pin` stays a list of INTEGERS (a pinned digest, not columns), never related.
            g = set()
            expr_cols(c["guard"], g)
            relate(g, "proof_bind:guard", i)  # relate() drops arity-1 sets itself
            if c.get("vk_pin") is not None:
                for lane in c["vk"]:
                    lane_cols = set(g)
                    expr_cols(lane, lane_cols)
                    relate(lane_cols, "proof_bind:vk_pin", i)
            if c.get("bound") is not None:
                for commit_lane, bound_lane in zip(c["commit"], c["bound"]):
                    lane_cols = set(g)
                    expr_cols(commit_lane, lane_cols)
                    expr_cols(bound_lane, lane_cols)
                    relate(lane_cols, "proof_bind:bound", i)
        elif t in ("mem_op", "map_op", "umem_op"):
            # ⚑ EXPRESSION SEQUENCES COUNT, NOT JUST SCALAR SLOTS (fixed 2026-08-05). These
            # tags carry their operands as bare `values()`, and until 2026-08-05 this walked only
            # the values that are THEMSELVES an expression dict — `map_op`'s `root`/`new_root` are
            # 8-element LISTS and every lane was invisible. ⚠ The `else` below refuses an unknown
            # TAG; nothing refused a known tag whose PAYLOAD grew a sequence, which is the quieter
            # half of the same hole.
            cols = set()
            for v in c.values():
                if isinstance(v, dict) and "t" in v:
                    expr_cols(v, cols)
                elif isinstance(v, list):
                    for item in v:
                        if isinstance(item, dict) and "t" in item:
                            expr_cols(item, cols)
            relate(cols, t, i)
        else:
            raise ValueError(f"unknown constraint tag {t!r} — the IR grew a form this gate cannot read")

    for s in d.get("hash_sites", []):
        cols = {s["digest_col"]}
        for inp in s["inputs"]:
            if inp["t"] == "col":
                cols.add(inp["c"])
        relate(cols, "hash_site", -1)
    for r in d.get("ranges", []):
        range_bits[r["wire"]].append(r["bits"])
        read[r["wire"]] += 1
        reads_by[r["wire"]].append((f"range_spec/{r['bits']}b", -1))

    comps: dict[int, list[int]] = collections.defaultdict(list)
    for c in range(width):
        comps[dsu.find(c)].append(c)
    touched = [c for c in range(width) if read[c] or c in pi]
    components = sorted(sorted(m for m in members if m in set(touched))
                        for members in comps.values()
                        if any(m in set(touched) for m in members))

    decorative = sorted(c for c in pi if related[c] == 0)
    return dict(
        name=d["name"], width=width, pi_count=d["public_input_count"],
        pi=pi, read=read, related=related, unary_gate=unary_gate,
        reads_by=dict(reads_by), range_bits=dict(range_bits), components=components,
        decorative=decorative,
        unread=sorted(c for c in decorative if read[c] == 0),
        untouched=[c for c in range(width) if not read[c] and c not in pi],
    )


def fmt_runs(cols) -> str:
    """`{0}{1}{2}{3}` / `{4..29}` — Solana's own notation."""
    cols = list(cols)
    if not cols:
        return "{}"
    runs, s, e = [], cols[0], cols[0]
    for c in cols[1:]:
        if c == e + 1:
            e = c
        else:
            runs.append((s, e))
            s = e = c
    runs.append((s, e))
    return "".join("{%d}" % a if a == b else "{%d..%d}" % (a, b) for a, b in runs)


def load_all(only: str | None = None):
    out = []
    for p in sorted(DESC_DIR.glob("*.json")):
        d = json.loads(p.read_text())
        if d.get("ir") != 2:
            continue
        if only and only not in d["name"]:
            continue
        out.append((p, analyze(d)))
    return out


def read_baseline() -> dict[str, int]:
    if not BASELINE.exists():
        return {}
    rows = {}
    for line in BASELINE.read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        n, name = line.split(None, 1)
        rows[name.strip()] = int(n)
    return rows


def write_baseline(entries):
    lines = [
        "# scripts/descriptor-anchor-inertness-baseline.txt — DECORATIVE PUBLIC INPUTS per served descriptor.",
        "#",
        "# A DECORATIVE anchor is a `pi_binding` column whose connected component in the",
        "# constraint graph is a SINGLETON: it co-occurs with no other column in any gate body,",
        "# boundary body, window-gate body, lookup tuple, hash site, transition or bus op. The",
        "# proof carries the value; nothing in the circuit is about it.",
        "#",
        "# ⚑ THESE NUMBERS MAY ONLY GO DOWN. Regenerate with",
        "#   scripts/check-descriptor-anchor-inertness.py --write-baseline",
        "# and say in the commit WHICH anchor became load-bearing and by what gate.",
        "#",
        "# `count  descriptor-name`; descriptors at zero are omitted.",
        "",
    ]
    for name, n in sorted(entries.items()):
        if n:
            lines.append(f"{n}\t{name}")
    BASELINE.write_text("\n".join(lines) + "\n")


def _desc(constraints, width=4, pi=2, tables=None):
    return dict(name="self-test", ir=2, trace_width=width, public_input_count=pi,
                tables=tables or [], constraints=constraints, hash_sites=[], ranges=[])


def self_test() -> int:
    """⚑ A GATE THAT CANNOT GO RED IS NOT A GATE. Three synthetic descriptors, three verdicts.

    Each case is the shape one real descriptor has, reduced to four columns."""
    V = lambda c: {"t": "var", "v": c}
    K = lambda k: {"t": "const", "v": k}
    ADD = lambda l, r: {"t": "add", "l": l, "r": r}
    PIN = lambda c, i: {"t": "pi_binding", "row": "first", "col": c, "pi_index": i}
    RANGE_TBL = [{"id": 9, "name": "range_w8", "arity": 1, "sem": "range", "bits": 8}]

    cases = []

    # (1) SOLANA'S SHAPE — the anchor is pinned to a PI and named nowhere else.
    cases.append(("anchor pinned and never named", _desc([
        {"t": "gate", "body": ADD(V(0), {"t": "mul", "l": K(-1), "r": V(1)})},
        PIN(2, 0), PIN(3, 1),
    ]), [2, 3]))

    # (2) MINA-VERIFY'S SHAPE — the anchor carries an arity-1 range lookup and nothing else.
    #     A width bound must NOT count as a binding, or the gate launders exactly this case.
    cases.append(("anchor read by an arity-1 range lookup only", _desc([
        {"t": "gate", "body": ADD(V(0), {"t": "mul", "l": K(-1), "r": V(1)})},
        {"t": "lookup", "table": 9, "tuple": [V(2)]},
        {"t": "lookup", "table": 9, "tuple": [V(3)]},
        PIN(2, 0), PIN(3, 1),
    ], tables=RANGE_TBL), [2, 3]))

    # (3) MINA-LINK'S SHAPE — a window gate joining `loc 2` to `nxt 3` is a REAL edge 2—3, so both
    #     anchors are related. If `loc`/`nxt` were treated as different columns this would misread.
    cases.append(("anchors joined by a two-row window gate", _desc([
        {"t": "window_gate", "on_transition": True,
         "body": ADD({"t": "loc", "c": 2}, {"t": "mul", "l": K(-1), "r": {"t": "nxt", "c": 3}})},
        PIN(2, 0), PIN(3, 1),
    ]), []))

    # (4) THE `pasta-*-sz` SHAPE — a `chal_gate` body `(loc 2 - loc 3)·α` joins 2—3 exactly as a
    #     plain gate does. Until 2026-08-10 this tag REFUSED the whole run (`unknown constraint
    #     tag 'chal_gate'`, exit 2, no comparison performed) from the hour the first four
    #     chal-carrying descriptors were routed into `by-name/`.
    CHAL = lambda i: {"t": "chal", "i": i}
    cases.append(("anchors joined by a chal_gate body", _desc([
        {"t": "chal_gate", "on_transition": False,
         "body": {"t": "mul",
                  "l": ADD({"t": "loc", "c": 2}, {"t": "mul", "l": K(-1), "r": {"t": "loc", "c": 3}}),
                  "r": CHAL(0)}},
        PIN(2, 0), PIN(3, 1),
    ]), []))

    # (5) THE MISREAD THAT WOULD LAUNDER IT — a challenge is a VERIFIER SCALAR, not a column. Two
    #     anchors each multiplied by the SAME `α` in separate one-column bodies share nothing; if
    #     `chal i` were walked as a column index, `α` would become a hub joining every anchor that
    #     touches it and this gate would report zero decorative anchors for every SZ descriptor.
    cases.append(("a challenge is not a column that joins anchors", _desc([
        {"t": "chal_gate", "on_transition": False,
         "body": {"t": "mul", "l": {"t": "loc", "c": 2}, "r": CHAL(0)}},
        {"t": "chal_gate", "on_transition": False,
         "body": {"t": "mul", "l": {"t": "loc", "c": 3}, "r": CHAL(0)}},
        PIN(2, 0), PIN(3, 1),
    ]), [2, 3]))

    ok = True
    for label, d, expected in cases:
        got = analyze(d)["decorative"]
        verdict = "PASS" if got == expected else "FAIL"
        ok &= got == expected
        print(f"  [{verdict}] {label}: decorative={got} expected={expected}")

    # (4) THE RATCHET ARM — a count above its baseline row must be REFUSED, not merely reported.
    base = {"self-test": 1}
    entries = {"self-test": 2}
    red = [n for n, v in entries.items() if v > base.get(n, 0)]
    print(f"  [{'PASS' if red else 'FAIL'}] a count above its baseline row reds: {red}")
    ok &= bool(red)

    print("check-descriptor-anchor-inertness --self-test: " + ("GREEN" if ok else "RED"))
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report", action="store_true", help="print the full decomposition")
    ap.add_argument("--carriers", action="store_true", help="also print single-column-gate columns")
    ap.add_argument("--only", help="substring filter on the descriptor name")
    ap.add_argument("--write-baseline", action="store_true")
    ap.add_argument("--self-test", action="store_true",
                    help="prove this gate can go red: three synthetic descriptors, three verdicts")
    args = ap.parse_args()

    if args.self_test:
        print(f"ANSWERS:         {SCOPE_ANSWERS_SELFTEST}", flush=True)
        print(f"DOES NOT ANSWER: {SCOPE_DOES_NOT_ANSWER_SELFTEST}", flush=True)
        return self_test()

    print(f"ANSWERS:         {SCOPE_ANSWERS}", flush=True)
    print(f"DOES NOT ANSWER: {SCOPE_DOES_NOT_ANSWER}", flush=True)

    try:
        found = load_all(args.only)
    except ValueError as e:
        print(f"REFUSING: {e}", file=sys.stderr)
        return 2
    if not found:
        print(f"REFUSING: no IR-v2 descriptors under {DESC_DIR}", file=sys.stderr)
        return 2

    if args.report:
        for _, a in found:
            print("=" * 96)
            print(f"{a['name']}   width={a['width']}  pi={a['pi_count']}  "
                  f"components={len(a['components'])}  decorative_anchors={len(a['decorative'])}")
            print("  " + "  /  ".join(fmt_runs(c) for c in a["components"]))
            if a["untouched"]:
                print(f"  UNTOUCHED (no constraint of any kind): {fmt_runs(a['untouched'])}")
            for col in sorted(a["pi"]):
                slots = ",".join(f"PI{i}@{r}" for i, r in a["pi"][col])
                if a["related"][col]:
                    comp = next(c for c in a["components"] if col in c)
                    verdict = f"connected: {fmt_runs(comp)}"
                elif not a["read"][col]:
                    verdict = "DECORATIVE, UNREAD — no constraint of any kind mentions it"
                else:
                    kinds = sorted({k for k, _ in a["reads_by"].get(col, [])})
                    verdict = ("DECORATIVE — a singleton component; the only constraints "
                               f"touching it relate it to no other column: {kinds}")
                print(f"    col {col:4d}  {slots:22s} {verdict}")
            if args.carriers:
                for col in sorted(a["unary_gate"]):
                    print(f"    carrier col {col:4d}: forced by {a['unary_gate'][col]}")
        return 0

    entries = {a["name"]: len(a["decorative"]) for _, a in found}
    if args.write_baseline:
        write_baseline(entries)
        print(f"wrote {BASELINE.relative_to(REPO)} "
              f"({sum(1 for v in entries.values() if v)} descriptors, "
              f"{sum(entries.values())} decorative anchors)")
        return 0

    base = read_baseline()
    if not base:
        print(f"REFUSING: {BASELINE.relative_to(REPO)} is missing or empty. "
              f"Run --write-baseline and commit it.", file=sys.stderr)
        return 2

    fail = []
    for name, n in sorted(entries.items()):
        b = base.get(name)
        if b is None:
            if n:
                fail.append(f"  UNLISTED  {name}: {n} decorative anchor(s) and no baseline row. "
                            f"A new descriptor may not be served with unbound public inputs.")
        elif n > b:
            fail.append(f"  ABOVE     {name}: {n} decorative anchor(s), baseline {b}. "
                        f"A public input stopped being related to anything.")
        elif n < b:
            fail.append(f"  STALE ROW {name}: {n} decorative anchor(s), baseline {b}. "
                        f"You bound an anchor — retire the row (--write-baseline).")
    for name in sorted(base):
        if name not in entries:
            fail.append(f"  GONE      {name}: baseline row for a descriptor no longer served. "
                        f"Retire the row (--write-baseline).")

    total = sum(entries.values())
    if fail:
        print("check-descriptor-anchor-inertness: RED", file=sys.stderr)
        print("\n".join(fail), file=sys.stderr)
        return 1
    print(f"check-descriptor-anchor-inertness: GREEN "
          f"({len(found)} IR-v2 descriptors, {total} decorative anchors at baseline)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
