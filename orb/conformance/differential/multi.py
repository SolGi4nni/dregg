#!/usr/bin/env python3
"""Multi-reference differential HTTP harness (3-way).

Sends one identical corpus of raw HTTP/1.1 requests to THREE servers:

    sut    the system under test (the target serve)
    caddy  reference A (stock caddy)
    h2o    reference B (stock h2o)

Each response is parsed, volatile headers normalized, and every response
dimension (status, content-type, content-encoding, framing, body, header set)
compared across all three. The point is to separate two very different kinds of
divergence:

  * STRONG GAP   the two references AGREE and the sut disagrees. When two
                 independently-implemented stock servers land on the same
                 answer and the sut does not, that is the strongest evidence of
                 a real behavioural gap in the sut.

  * REF-SPECIFIC the sut disagrees with exactly ONE reference; the two
                 references themselves disagree on that dimension. This is
                 usually a config/opinion difference (MIME table, gzip policy,
                 error-page wording), not a sut gap.

  * REF-SPLIT    the two references disagree AND the sut matches neither, or the
                 references disagree and the sut picks a side. Reported as
                 context, not scored as a sut gap.

Nothing here tunes for a pass. Divergences are the deliverable.

This module DELIBERATELY reuses the corpus, request builder, response parser and
volatile-header policy from the sibling two-way harness (diff.py) so the two
lanes stay in lock-step — extending one corpus extends both.

Usage:
    multi.py [--host H] [--sut-port N] [--caddy-port N] [--h2o-port N]
             [--json OUT] [--show-same]
"""
import argparse
import hashlib
import json
import os
import sys

# Reuse the two-way harness as a library (same directory).
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import diff  # noqa: E402  (corpus + parser + volatile policy live here)

SERVERS = ("sut", "caddy", "h2o")


def sha12(b):
    return hashlib.sha256(b).hexdigest()[:12]


def state_of(resp):
    """resp is a parsed tuple, None (unparseable), or an error string."""
    if isinstance(resp, str):
        return ("error", resp)
    if resp is None:
        return ("unparseable", None)
    return ("ok", None)


def header_map(headers):
    """name -> tuple(values) with volatile VALUES masked, volatile-presence
    names dropped entirely. Mirrors diff.norm_headers + presence policy."""
    out = {}
    for k, v in headers:
        if k in diff.VOLATILE_PRESENCE:
            continue
        val = "<vol>" if k in diff.VOLATILE_VALUE else v
        out.setdefault(k, []).append(val)
    return {k: tuple(v) for k, v in out.items()}


def dims(resp):
    """Extract the comparable dimensions of one response into a flat dict.

    Every value is hashable so cross-server comparison is a plain ==. Absent
    dimensions map to None so 'present here, absent there' is a real diff.
    """
    st, detail = state_of(resp)
    if st != "ok":
        # A non-ok transport state collapses to a single dimension; comparing
        # it against an ok peer yields a transport-level divergence.
        return {"transport": f"{st}:{detail}" if detail else st}

    status_line, headers, body = resp
    hm = header_map(headers)
    d = {
        "transport": "ok",
        "status": diff.status_code(status_line),
        "content-type": hm.get("content-type"),
        "content-encoding": hm.get("content-encoding"),
        "transfer-encoding": hm.get("transfer-encoding"),
        "content-length": hm.get("content-length"),
        "accept-ranges": hm.get("accept-ranges"),
        "content-range": hm.get("content-range"),
        "allow": hm.get("allow"),
        "vary": hm.get("vary"),
        "location": hm.get("location"),
        # Full non-volatile header-name set (presence-only signal).
        "header-set": tuple(sorted(hm.keys())),
        # Body identity. For HEAD/304/204 the body is empty on all sides.
        "body": (len(body), sha12(body)),
    }
    return d


# Human weighting for ranking: higher = a more consequential dimension.
DIM_RANK = {
    "transport": 100,
    "status": 90,
    "content-range": 70,
    "accept-ranges": 55,
    "content-encoding": 60,
    "transfer-encoding": 58,
    "content-length": 50,
    "location": 65,
    "allow": 45,
    "content-type": 40,
    "vary": 30,
    "body": 80,
    "header-set": 20,
}
ALL_DIMS = list(DIM_RANK.keys())


def classify(sv, cv, hv):
    """Classify one dimension across (sut, caddy, h2o) values.

    Returns (kind, note) or None if all three agree.
      strong-gap    : caddy == h2o != sut          (references agree, sut alone)
      ref-specific  : sut differs from exactly one; refs also differ
      ref-split     : refs disagree and sut matches neither
    """
    if sv == cv == hv:
        return None
    refs_agree = (cv == hv)
    diff_caddy = (sv != cv)
    diff_h2o = (sv != hv)

    if refs_agree:
        # Both references landed the same place, sut did not.
        return ("strong-gap", "refs agree; sut alone")
    # References disagree with each other.
    if diff_caddy and diff_h2o:
        return ("ref-split", "refs disagree; sut matches neither")
    if diff_caddy and not diff_h2o:
        return ("ref-specific", "sut differs from caddy; matches h2o")
    if diff_h2o and not diff_caddy:
        return ("ref-specific", "sut differs from h2o; matches caddy")
    # sut equals both but cv!=hv can't happen (would mean sv==cv and sv==hv).
    return ("ref-split", "refs disagree; sut matches both?")


KIND_ORDER = {"strong-gap": 0, "ref-specific": 1, "ref-split": 2}


def fmt(v):
    if v is None:
        return "-"
    if isinstance(v, tuple):
        return "/".join(str(x) for x in v) if v else "()"
    return str(v)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--sut-port", type=int, default=18950)
    ap.add_argument("--caddy-port", type=int, default=18951)
    ap.add_argument("--h2o-port", type=int, default=18952)
    ap.add_argument("--json", default=None)
    ap.add_argument("--show-same", action="store_true")
    args = ap.parse_args()

    ports = {"sut": args.sut_port, "caddy": args.caddy_port, "h2o": args.h2o_port}
    corpus = diff.build_corpus(args.host, 0, 0)

    results = []
    counts = {"strong-gap": 0, "ref-specific": 0, "ref-split": 0}
    n_clean = 0

    for cid, cat, desc, raw in corpus:
        resp = {}
        dd = {}
        for name in SERVERS:
            port = ports[name]
            wire = raw.replace(b"{HOST}", f"{args.host}:{port}".encode())
            rawb, err = diff.recv_all(args.host, port, wire)
            parsed = err if err else diff.parse_response(rawb)
            resp[name] = parsed
            dd[name] = dims(parsed)

        # Per-dimension classification.
        findings = []
        all_keys = set()
        for name in SERVERS:
            all_keys |= set(dd[name].keys())
        for k in all_keys:
            sv, cv, hv = dd["sut"].get(k), dd["caddy"].get(k), dd["h2o"].get(k)
            verdict = classify(sv, cv, hv)
            if verdict is None:
                continue
            kind, note = verdict
            findings.append({
                "dim": k, "kind": kind, "note": note,
                "rank": DIM_RANK.get(k, 10),
                "sut": fmt(sv), "caddy": fmt(cv), "h2o": fmt(hv),
            })

        findings.sort(key=lambda f: (KIND_ORDER[f["kind"]], -f["rank"]))
        for f in findings:
            counts[f["kind"]] += 1
        if not findings:
            n_clean += 1

        def sline(name):
            r = resp[name]
            return r[0] if isinstance(r, tuple) else f"ERR:{r}"

        results.append({
            "id": cid, "category": cat, "desc": desc,
            "status_lines": {n: sline(n) for n in SERVERS},
            "findings": findings,
        })

    # ---- report ----------------------------------------------------------
    print(f"\n=== 3-way differential: {len(corpus)} requests ===")
    print(f"    sut :{args.sut_port}   caddy :{args.caddy_port}   h2o :{args.h2o_port}\n")

    # Strong gaps first (the headline: refs agree, sut alone).
    strong = [(r, f) for r in results for f in r["findings"] if f["kind"] == "strong-gap"]
    strong.sort(key=lambda rf: -rf[1]["rank"])
    print(f"--- STRONG GAPS ({len(strong)}): references AGREE, sut disagrees ---")
    if not strong:
        print("    (none)")
    for r, f in strong:
        print(f"  [{f['dim']}] {r['id']} ({r['category']})  {r['desc']}")
        print(f"      sut={f['sut']}  caddy={f['caddy']}  h2o={f['h2o']}")
    print()

    print("--- REF-SPECIFIC / REF-SPLIT (context, not scored as sut gaps) ---")
    other = [(r, f) for r in results for f in r["findings"] if f["kind"] != "strong-gap"]
    other.sort(key=lambda rf: (KIND_ORDER[rf[1]["kind"]], -rf[1]["rank"]))
    if not other:
        print("    (none)")
    for r, f in other:
        print(f"  {f['kind']:12s} [{f['dim']}] {r['id']}: "
              f"sut={f['sut']} caddy={f['caddy']} h2o={f['h2o']}  ({f['note']})")
    print()

    # Per-request roll-up.
    if args.show_same:
        print("--- per-request status lines ---")
        for r in results:
            tag = "CLEAN" if not r["findings"] else \
                  ("GAP" if any(f["kind"] == "strong-gap" for f in r["findings"]) else "diff")
            print(f"  [{tag:5s}] {r['id']}")
            for n in SERVERS:
                print(f"      {n:5s}: {r['status_lines'][n]}")
        print()

    print("=== summary ===")
    print(f"  requests            : {len(corpus)}")
    print(f"  clean (all 3 agree) : {n_clean}")
    print(f"  strong-gap findings : {counts['strong-gap']}  (sut vs both refs)")
    print(f"  ref-specific        : {counts['ref-specific']}")
    print(f"  ref-split           : {counts['ref-split']}")
    n_gap_reqs = sum(1 for r in results if any(f["kind"] == "strong-gap" for f in r["findings"]))
    print(f"  requests w/ >=1 strong gap : {n_gap_reqs}/{len(corpus)}")

    if args.json:
        with open(args.json, "w") as f:
            json.dump({"summary": {"requests": len(corpus), "clean": n_clean,
                                   "counts": counts, "gap_requests": n_gap_reqs},
                       "results": results}, f, indent=2)
        print(f"wrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
