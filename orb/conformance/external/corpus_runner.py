#!/usr/bin/env python3
"""External structured-fields conformance runner (RFC 8941 / RFC 9218 / RFC 9211).

Imports a real, external reference test corpus (the httpwg structured-field-tests
battery: a data-driven RFC 8941 Structured Fields parse/serialise suite) and runs
it against the live target serve over the wire. It is not a hand-written check: the
cases are the upstream reference vectors, unmodified.

Three batteries:

  ORACLE   Validate the harness's own RFC 8941 parser (sf8941.py) against the full
           corpus, so its verdicts on the target's produced fields are trustworthy.
           Pass = parser rejects every `must_fail` vector and accepts every
           well-formed vector. This scores the ORACLE, not the target.

  CONSUME  Feed the corpus at the target over the wire on the `priority` request
           header (RFC 9218 Extensible Priorities defines that value as an RFC 8941
           Dictionary). Each dictionary vector is sent as a `priority:` header on a
           real request. IMPORTANT / gap map: the target's SF Dictionary parser is
           proven in the model but NOT wired into any live datapath (no ingress
           call site), and priority is an H2/H3 scheduling signal with no HTTP/1.1
           observable, so this battery does NOT exercise the SF parser — it measures
           the serve's ROBUSTNESS to an arbitrary adversarial/malformed extra header
           (no 5xx / reset / timeout; per RFC 9218 §4 an unrecognized/invalid
           priority is ignored). Kept because it is the honest wire truth and turns
           green into a real signal only once the parser is wired.

  PRODUCE  Validate the structured fields the target EMITS. The target produces
           `Cache-Status` (RFC 9211, an SF List) and `Permissions-Policy` (an SF
           Dictionary). Their emitted values are parsed with the corpus-validated
           oracle; pass = the emitted value is well-formed SF of its declared type.

Honesty: every pass/fail below is from an actual socket round-trip or an actual
parser run performed by this script. Failures are findings (the gap map), not
harness errors. Exit code is always 0.

Usage:
    python3 corpus_runner.py [--corpus DIR] [--host H] [--port P] [--out FILE]
"""
import argparse
import glob
import json
import os
import socket
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sf8941


# --------------------------------------------------------------------------- I/O

def raw_roundtrip(host, port, req, timeout=4.0, cap=1 << 20):
    """Send raw bytes on a fresh connection; return (bytes, error_str_or_None)."""
    try:
        s = socket.create_connection((host, port), timeout=timeout)
    except Exception as e:
        return None, "connect:%s" % type(e).__name__
    s.settimeout(timeout)
    try:
        s.sendall(req)
        buf = b""
        while len(buf) < cap:
            try:
                d = s.recv(65536)
            except socket.timeout:
                return buf, "timeout"
            if not d:
                break
            buf += d
        return buf, None
    except Exception as e:
        return None, "io:%s" % type(e).__name__
    finally:
        try:
            s.close()
        except Exception:
            pass


def status_code(resp):
    if not resp:
        return None
    line = resp.split(b"\r\n", 1)[0]
    parts = line.split(b" ", 2)
    if len(parts) >= 2 and parts[1].isdigit():
        return int(parts[1])
    return None


def header_value(resp, name):
    head = (resp or b"").split(b"\r\n\r\n", 1)[0]
    key = name.lower().encode() + b":"
    for ln in head.split(b"\r\n")[1:]:
        if ln.lower().startswith(key):
            return ln[len(key):].strip().decode("latin1")
    return None


# ----------------------------------------------------------------- corpus loading

def load_corpus(corpus_dir):
    cases = []
    for f in sorted(glob.glob(os.path.join(corpus_dir, "*.json"))):
        base = os.path.basename(f)
        if base.startswith("schema") or "schema" in f.replace(base, ""):
            continue
        try:
            data = json.load(open(f))
        except Exception:
            continue
        if not isinstance(data, list):
            continue
        for c in data:
            if isinstance(c, dict) and "header_type" in c:
                c["_file"] = base
                cases.append(c)
    return cases


def raw_value(case):
    """The field value as it goes on the wire: field-lines joined per RFC (", ")."""
    return ", ".join(case.get("raw", []))


def sendable(value):
    """A value is sendable as an HTTP/1.1 header line iff it has no CR/LF/NUL and is
    ASCII-representable. Non-sendable vectors exercise HTTP lexing, not SF parsing,
    so they are reported UNSENDABLE rather than scored."""
    if any(ord(ch) > 0xFF for ch in value):
        return False
    b = value.encode("latin1", "replace")
    return b"\r" not in b and b"\n" not in b and b"\x00" not in b


# ------------------------------------------------------------------- ORACLE battery

def _norm(v):
    """Normalize the oracle's parse output into the corpus's expected JSON shape.

    Corpus shape: item=[bare,params]; params=[[k,v],...]; token/binary/date/
    displaystring = {"__type":..,"value":..}; list=[member,...]; inner-list=
    [[item,...],params]; dict=[[key,member],...]."""
    if isinstance(v, tuple):
        return [_norm(x) for x in v]
    if isinstance(v, list):
        return [_norm(x) for x in v]
    if isinstance(v, dict):
        return {"__type": v["__type"], "value": v["value"]}
    if isinstance(v, bool):
        return v
    return v


def battery_oracle(cases):
    # ast-equality is the strong check: on every non-failing vector the oracle must
    # reproduce the corpus's expected AST, not merely accept the input. must_fail
    # vectors must raise. can_fail vectors may do either.
    results = {"pass": 0, "fail": 0, "skip": 0, "ast_checked": 0, "detail": []}
    parse = {"item": sf8941.parse_item, "list": sf8941.parse_list,
             "dictionary": sf8941.parse_dictionary}
    for c in cases:
        ht = c["header_type"]
        fn = parse.get(ht)
        if fn is None:
            results["skip"] += 1
            continue
        must_fail = bool(c.get("must_fail"))
        can_fail = bool(c.get("can_fail"))
        val = raw_value(c)
        raised = False
        parsed = None
        try:
            parsed = fn(val)
        except Exception:
            raised = True
        if can_fail:
            ok = True
        elif must_fail:
            ok = raised
        else:
            ok = not raised
            if ok and "expected" in c:
                # strong AST-equality on well-formed, deterministically-parsed cases
                results["ast_checked"] += 1
                got = _norm(parsed)
                if json.loads(json.dumps(got)) != c["expected"]:
                    ok = False
                    if len(results["detail"]) < 60:
                        results["detail"].append({
                            "file": c["_file"], "name": c.get("name"), "type": ht,
                            "reason": "ast-mismatch", "raw": val[:80],
                            "got": got, "expected": c["expected"]})
                    results["fail"] += 1
                    continue
        if ok:
            results["pass"] += 1
        else:
            results["fail"] += 1
            if len(results["detail"]) < 60:
                results["detail"].append({
                    "file": c["_file"], "name": c.get("name"), "type": ht,
                    "must_fail": must_fail, "raised": raised, "raw": val[:80],
                })
    return results


# ------------------------------------------------------------------ CONSUME battery

def _baseline_status(host, port, route):
    """Status the route returns with NO priority header — the reference for
    detecting whether the structured input changes observable behavior."""
    req = ("GET %s HTTP/1.1\r\nHost: 127.0.0.1:%d\r\nConnection: close\r\n\r\n"
           % (route, port)).encode()
    resp, _ = raw_roundtrip(host, port, req)
    return status_code(resp)


def battery_consume(cases, host, port, route="/static/probe.txt"):
    """Feed each Dictionary vector as a `priority:` request header at the target."""
    dict_cases = [c for c in cases if c["header_type"] == "dictionary"]
    baseline = _baseline_status(host, port, route)
    out = {"total": len(dict_cases), "pass": 0, "fail": 0, "unsendable": 0,
           "route": route, "baseline_status": baseline, "status_hist": {},
           "fail_detail": [], "status_differs": 0, "differs_detail": []}
    for c in dict_cases:
        val = raw_value(c)
        if not sendable(val):
            out["unsendable"] += 1
            continue
        req = (
            "GET %s HTTP/1.1\r\nHost: 127.0.0.1:%d\r\n"
            "priority: %s\r\nConnection: close\r\n\r\n" % (route, port, val)
        ).encode("latin1")
        resp, err = raw_roundtrip(host, port, req)
        code = status_code(resp)
        # Robustness (RFC 9218 §4: invalid priority is IGNORED, request proceeds):
        # PASS = stable HTTP response, no 5xx / reset / timeout. This is the only
        # semantics observable on the HTTP/1.1 datapath (parsed priority steers
        # H2/H3 scheduling, not the /1.1 response — see gap map).
        robust = err is None and code is not None and code < 500
        key = str(code) if code is not None else ("ERR:" + (err or "?"))
        out["status_hist"][key] = out["status_hist"].get(key, 0) + 1
        if robust:
            out["pass"] += 1
            # An observable behavior change vs baseline would be the only positive
            # datapath signal; flag it (expected: none, since /1.1 ignores priority).
            if code != baseline:
                out["status_differs"] += 1
                if len(out["differs_detail"]) < 20:
                    out["differs_detail"].append(
                        {"name": c.get("name"), "code": code,
                         "baseline": baseline, "raw": val[:80]})
        else:
            out["fail"] += 1
            if len(out["fail_detail"]) < 40:
                out["fail_detail"].append(
                    {"name": c.get("name"), "err": err, "code": code, "raw": val[:80]})
    return out


def battery_consume_fuzz(cases, host, port, route="/static/probe.txt"):
    """Broad robustness sweep: feed EVERY sendable corpus vector (item/list/dict)
    as a `priority:` header. Over-typed on purpose — pure input hardening."""
    out = {"total": 0, "pass": 0, "fail": 0, "unsendable": 0, "fail_detail": []}
    for c in cases:
        val = raw_value(c)
        out["total"] += 1
        if not sendable(val):
            out["unsendable"] += 1
            continue
        req = (
            "GET %s HTTP/1.1\r\nHost: 127.0.0.1:%d\r\n"
            "priority: %s\r\nConnection: close\r\n\r\n" % (route, port, val)
        ).encode("latin1")
        resp, err = raw_roundtrip(host, port, req)
        code = status_code(resp)
        if err is None and code is not None and code < 500:
            out["pass"] += 1
        else:
            out["fail"] += 1
            if len(out["fail_detail"]) < 40:
                out["fail_detail"].append(
                    {"name": c.get("name"), "err": err, "code": code, "raw": val[:80]})
    return out


# ------------------------------------------------------------------ PRODUCE battery

PRODUCED = [
    # (response header name, RFC 8941 type, source RFC)
    ("Cache-Status", "list", "RFC 9211"),
    ("Permissions-Policy", "dictionary", "RFC 9218-style / Permissions Policy"),
    ("Alt-Svc", "dictionary", "RFC 7838 (SF-ish)"),
]


def battery_produce(host, port):
    routes = ["/", "/static/probe.txt", "/index.html", "/api/status"]
    parse = {"item": sf8941.parse_item, "list": sf8941.parse_list,
             "dictionary": sf8941.parse_dictionary}
    out = {"fields": [], "pass": 0, "fail": 0, "absent": 0}
    seen = {}
    for route in routes:
        req = ("GET %s HTTP/1.1\r\nHost: 127.0.0.1:%d\r\nConnection: close\r\n\r\n"
               % (route, port)).encode()
        resp, err = raw_roundtrip(host, port, req)
        if resp is None:
            continue
        for name, ht, rfc in PRODUCED:
            v = header_value(resp, name)
            if v is None:
                continue
            k = (name, v)
            if k in seen:
                continue
            seen[k] = True
            rec = {"header": name, "rfc": rfc, "sf_type": ht, "route": route,
                   "value": v}
            try:
                parse[ht](v)
                rec["verdict"] = "PASS"
                out["pass"] += 1
            except Exception as e:
                rec["verdict"] = "FAIL"
                rec["error"] = str(e)
                out["fail"] += 1
            out["fields"].append(rec)
    for name, ht, rfc in PRODUCED:
        if not any(f["header"] == name for f in out["fields"]):
            out["absent"] += 1
    return out


# ----------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", default=os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "structured-field-tests"))
    ap.add_argument("--host", default=os.environ.get("CONF_HTTP_HOST", "127.0.0.1"))
    ap.add_argument("--port", type=int,
                    default=int(os.environ.get("CONF_SF_PORT", "18950")))
    ap.add_argument("--out", default=os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "results_sf.json"))
    ap.add_argument("--no-serve", action="store_true",
                    help="oracle self-check only; do not contact the target")
    args = ap.parse_args()

    cases = load_corpus(args.corpus)
    report = {"corpus_dir": args.corpus, "n_cases": len(cases),
              "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}

    # by header_type
    ht = {}
    for c in cases:
        ht[c["header_type"]] = ht.get(c["header_type"], 0) + 1
    report["by_header_type"] = ht

    print("== external structured-fields conformance ==")
    print("corpus: %s" % args.corpus)
    print("cases:  %d  (%s)" % (len(cases), ht))

    print("\n-- ORACLE (harness RFC 8941 parser vs corpus) --")
    orc = battery_oracle(cases)
    report["oracle"] = orc
    scored = orc["pass"] + orc["fail"]
    print("  pass %d / %d  (fail %d, skipped-type %d; ast-equality checked on %d)" %
          (orc["pass"], scored, orc["fail"], orc["skip"], orc["ast_checked"]))

    if not args.no_serve:
        # reachability
        resp, err = raw_roundtrip(args.host, args.port,
                                  b"GET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
        if resp is None:
            print("\n!! target not reachable on %s:%d (%s) — running oracle only"
                  % (args.host, args.port, err))
            report["target_reachable"] = False
        else:
            report["target_reachable"] = True
            print("\n-- CONSUME (corpus Dictionary vectors -> target `priority` header) --")
            con = battery_consume(cases, args.host, args.port)
            report["consume"] = con
            print("  robust %d / %d  (fail %d, unsendable %d)" %
                  (con["pass"], con["total"] - con["unsendable"], con["fail"],
                   con["unsendable"]))
            print("  baseline status (no priority hdr): %s" % con["baseline_status"])
            print("  status histogram: %s" % con["status_hist"])
            print("  responses differing from baseline: %d" % con["status_differs"])

            print("\n-- CONSUME-FUZZ (all corpus vectors -> target `priority` header) --")
            fuzz = battery_consume_fuzz(cases, args.host, args.port)
            report["consume_fuzz"] = fuzz
            print("  robust %d / %d  (fail %d, unsendable %d)" %
                  (fuzz["pass"], fuzz["total"] - fuzz["unsendable"], fuzz["fail"],
                   fuzz["unsendable"]))

            print("\n-- PRODUCE (target-emitted SF response headers vs RFC 8941) --")
            pro = battery_produce(args.host, args.port)
            report["produce"] = pro
            for f in pro["fields"]:
                print("  [%s] %-20s %-10s %r" %
                      (f["verdict"], f["header"], f["sf_type"], f["value"][:60]))
            print("  well-formed %d / %d" % (pro["pass"], pro["pass"] + pro["fail"]))
    else:
        report["target_reachable"] = None

    json.dump(report, open(args.out, "w"), indent=2)
    print("\nwrote %s" % args.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
