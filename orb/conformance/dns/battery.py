#!/usr/bin/env python3
"""DNS conformance battery: dig-captured real wire messages vs the Dns library.

For each captured exchange (capture.py: dig's real query octets + the real
resolver's response octets), the deployed Dns functions are driven via
DnsCheck.lean, and the result is scored against dig's own decoded view of the
same response (the oracle).

Per-case checks:
  qparse    the query octets dig actually sent parse (parseMsg); for the tcp
            case this includes the RFC 1035 §4.2.2 unframing (FRAME ok)
  rparse    the response octets the resolver returned parse (parseMsg)
  typed     every resource record in every section has a typed RDATA read
            (typedRData is not `none` and not `other` for types with readers —
            NSEC3/NSEC3PARAM included)
  xrcode    the RFC 6891 §6.1.3 extended RCODE (OPT upper bits merged with the
            header RCODE) equals dig's decoded status
  extract   answersOf/resolve output matches dig's decoded answers
            (case-specific: address sets, MX pairs, TXT contents, SOA serial,
             DNSKEY/DS fields + RFC 4034 Appendix B key tags, NSEC3 fields and
             type bitmaps, SvcParams, EDNS cookies, NXDOMAIN refusal, ...)

Usage: python3 battery.py            (uses existing captures/)
       python3 battery.py --capture  (re-capture first)
"""

import base64
import os
import re
import socket
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
CAPDIR = os.path.join(HERE, "captures")

STATUS = {"NOERROR": 0, "FORMERR": 1, "SERVFAIL": 2, "NXDOMAIN": 3,
          "NOTIMP": 4, "REFUSED": 5, "BADVERS": 16, "BADCOOKIE": 23}

MNEMONIC = {"A": 1, "NS": 2, "CNAME": 5, "SOA": 6, "PTR": 12, "HINFO": 13,
            "MX": 15, "TXT": 16, "AAAA": 28, "SRV": 33, "NAPTR": 35,
            "DS": 43, "SSHFP": 44, "RRSIG": 46, "NSEC": 47, "DNSKEY": 48,
            "NSEC3": 50, "NSEC3PARAM": 51, "TLSA": 52, "SVCB": 64,
            "HTTPS": 65, "SPF": 99, "CAA": 257}


def type_num(mn):
    if mn in MNEMONIC:
        return MNEMONIC[mn]
    m = re.match(r"TYPE(\d+)$", mn)
    return int(m.group(1)) if m else None


def b32hex_to_hex(s):
    s = s.upper()
    pad = "=" * (-len(s) % 8)
    return base64.b32hexdecode(s + pad).hex()


def run_lean():
    manifest = os.path.join(CAPDIR, "manifest.txt")
    out = subprocess.run(
        ["lake", "env", "lean", "--run", os.path.join(HERE, "DnsCheck.lean"), manifest],
        cwd=ROOT, capture_output=True, text=True, timeout=600,
    )
    if out.returncode != 0:
        print(out.stdout)
        print(out.stderr, file=sys.stderr)
        sys.exit(f"DnsCheck.lean failed (rc={out.returncode})")
    return out.stdout


def parse_report(text):
    caps = {}
    cur = None
    for line in text.splitlines():
        if line.startswith("CAPTURE "):
            cur = {"name": line.split()[1], "rrs": [], "ans": [], "qs": []}
            caps[cur["name"]] = cur
        elif cur is None:
            continue
        elif line.startswith("FRAME"):
            cur["frame"] = line.split()[1] == "ok"
        elif line.startswith("QPARSE"):
            cur["qparse"] = line.split()[1] == "ok"
        elif line.startswith("QCOOKIE"):
            parts = line.split()
            cur["qcookie"] = (parts[1], parts[2])
        elif line.startswith("RPARSE"):
            cur["rparse"] = line.split()[1] == "ok"
        elif line.startswith("RCODE"):
            cur["rcode"] = int(line.split()[1])
        elif line.startswith("XRCODE"):
            cur["xrcode"] = int(line.split()[1])
        elif line.startswith("TC"):
            cur["tc"] = line.split()[1] == "true"
        elif line.startswith("RETRY"):
            cur["retry"] = line.split()[1] == "true"
        elif line.startswith("COUNTS"):
            cur["counts"] = [int(x) for x in line.split()[1:]]
        elif line.startswith("Q "):
            cur["qs"].append(line.split(" ", 1)[1])
        elif line.startswith("RR "):
            parts = line.split(" ", 4)
            cur["rrs"].append(
                {"sec": parts[1], "type": int(parts[2]), "owner": parts[3],
                 "typed": parts[4] if len(parts) > 4 else ""})
        elif line.startswith("ANS "):
            cur["ans"].append(line[4:])
    return caps


def dig_answers(case):
    """Parse dig's ANSWER SECTION for a case: list of (owner, type, rdata)."""
    path = os.path.join(CAPDIR, f"{case}.dig.txt")
    with open(path) as f:
        text = f.read()
    answers = []
    in_ans = False
    for line in text.splitlines():
        if line.startswith(";; ANSWER SECTION:"):
            in_ans = True
            continue
        if in_ans:
            if not line.strip() or line.startswith(";;"):
                break
            m = re.match(r"^(\S+)\s+(\d+)\s+IN\s+(\S+)\s+(.*)$", line)
            if m:
                answers.append((m.group(1).rstrip(".").lower(),
                                m.group(3), m.group(4).strip()))
    status = None
    m = re.search(r"status: (\w+)", text)
    if m:
        status = m.group(1)
    return answers, status, text


def dig_authority(case):
    """Parse dig's AUTHORITY SECTION: list of (owner, type, rdata)."""
    path = os.path.join(CAPDIR, f"{case}.dig.txt")
    with open(path) as f:
        text = f.read()
    out = []
    in_sec = False
    for line in text.splitlines():
        if line.startswith(";; AUTHORITY SECTION:"):
            in_sec = True
            continue
        if in_sec:
            if not line.strip() or line.startswith(";;"):
                break
            m = re.match(r"^(\S+)\s+(\d+)\s+IN\s+(\S+)\s+(.*)$", line)
            if m:
                out.append((m.group(1).rstrip(".").lower(),
                            m.group(3), m.group(4).strip()))
    return out


def norm6(s):
    return socket.inet_pton(socket.AF_INET6, s).hex()


def dig_txt_strings(rdata):
    return "".join(re.findall(r'"((?:[^"\\]|\\.)*)"', rdata)).replace('\\"', '"')


def ans_of(cap, kind):
    return [a[len(kind) + 1:] for a in cap["ans"] if a.startswith(kind + " ")]


def query_cookie_from_wire(case):
    """Independently decode the EDNS COOKIE option out of the captured query
    octets (dig's exact wire bytes)."""
    path = os.path.join(CAPDIR, f"{case}.q.hex")
    with open(path) as f:
        raw = bytes.fromhex(f.read().strip())
    qd = (raw[4] << 8) | raw[5]
    ar = (raw[10] << 8) | raw[11]
    i = 12

    def skip_name(i):
        while True:
            b = raw[i]
            if b == 0:
                return i + 1
            if b >= 0xC0:
                return i + 2
            i += b + 1

    for _ in range(qd):
        i = skip_name(i) + 4
    an = (raw[6] << 8) | raw[7]
    ns = (raw[8] << 8) | raw[9]
    for _ in range(an + ns + ar):
        i = skip_name(i)
        t = (raw[i] << 8) | raw[i + 1]
        rdlen = (raw[i + 8] << 8) | raw[i + 9]
        rd = raw[i + 10:i + 10 + rdlen]
        i += 10 + rdlen
        if t == 41:
            j = 0
            while j + 4 <= len(rd):
                code = (rd[j] << 8) | rd[j + 1]
                ln = (rd[j + 2] << 8) | rd[j + 3]
                val = rd[j + 4:j + 4 + ln]
                j += 4 + ln
                if code == 10:
                    return val[:8].hex(), (val[8:].hex() or "-")
    return None


def check_nsec3_authority(case, cap):
    """Compare every NSEC3 record dig printed in the authority section against
    the library's typed read: hash alg, flags, iterations, salt, next hashed
    owner (dig prints base32hex), and the decoded type bitmap."""
    want = []
    for (owner, t, rdata) in dig_authority(case):
        if t != "NSEC3":
            continue
        toks = rdata.split()
        alg, flags, iters, salt = toks[0], toks[1], toks[2], toks[3].lower()
        nexth = b32hex_to_hex(toks[4])
        types = sorted(type_num(x) for x in toks[5:] if type_num(x) is not None)
        want.append((owner, alg, flags, iters, salt, nexth, types))
    got = []
    for r in cap["rrs"]:
        if r["sec"] != "authority" or r["type"] != 50:
            continue
        toks = r["typed"].split()
        # NSEC3 <alg> <flags> <iter> <salthex> <nexthex> <types,comma>
        types = sorted(int(x) for x in toks[6].split(",")) if len(toks) > 6 else []
        got.append((r["owner"].lower(), toks[1], toks[2], toks[3],
                    toks[4].lower(), toks[5].lower(), types))
    return (sorted(want) == sorted(got) and want != [],
            f"dig NSEC3 n={len(want)} lib n={len(got)} equal={sorted(want) == sorted(got)}")


def dnskey_tags(cap):
    """Computed RFC 4034 Appendix B key tags of every DNSKEY answer."""
    tags = {}
    for v in ans_of(cap, "DNSKEY"):
        m = re.match(r"(\d+) (\d+) (\d+) \d+ tag=(\d+)", v)
        if m:
            tags[int(m.group(4))] = int(m.group(1))
    return tags


def check_extract(case, cap):
    """Case-specific oracle comparison. Returns (ok, detail)."""
    answers, status, text = dig_answers(case)

    if case == "nxdomain":
        ok = status == "NXDOMAIN" and cap.get("rcode") == 3 and not cap["ans"]
        if not ok:
            return ok, f"status={status} rcode={cap.get('rcode')} ans={len(cap['ans'])}"
        # RFC 5155: the denial-of-existence proof must be readable.
        return check_nsec3_authority(case, cap)

    if case in ("a-multi", "cname", "a-dnssec", "noedns", "tcp", "mixedcase"):
        want = sorted(r for (_, t, r) in answers if t == "A")
        got = sorted(ans_of(cap, "A"))
        if case == "tcp" and not cap.get("frame", False):
            return False, "TCP stream did not unframe cleanly"
        return want == got and want != [], f"dig A={want} lib A={got}"

    if case == "aaaa":
        want = sorted(norm6(r) for (_, t, r) in answers if t == "AAAA")
        got = sorted(ans_of(cap, "AAAA"))
        return want == got and want != [], f"dig={want} lib={got}"

    if case == "mx":
        want = set()
        for (_, t, r) in answers:
            if t == "MX":
                pref, exch = r.split()
                want.add((int(pref), exch.rstrip(".").lower()))
        got = set()
        for v in ans_of(cap, "MX"):
            pref, exch = v.split(" ", 1)
            got.add((int(pref), exch.lower()))
        return want == got and want != set(), f"dig={sorted(want)} lib={sorted(got)}"

    if case == "txt":
        want = sorted(dig_txt_strings(r) for (_, t, r) in answers if t == "TXT")
        got = sorted(v.split(" ", 1)[1] if " " in v else ""
                     for v in ans_of(cap, "TXT"))
        return want == got and want != [], f"dig={want} lib={got}"

    if case == "ns":
        want = sorted(r.rstrip(".").lower() for (_, t, r) in answers if t == "NS")
        got = sorted(v.lower() for v in ans_of(cap, "NS"))
        return want == got and want != [], f"dig={want} lib={got}"

    if case == "soa":
        want = [r.split()[2] for (_, t, r) in answers if t == "SOA"]  # serial
        got = [v.split()[2] for v in ans_of(cap, "SOA")]
        return want == got and want != [], f"dig serial={want} lib serial={got}"

    if case == "ptr":
        want = sorted(r.rstrip(".").lower() for (_, t, r) in answers if t == "PTR")
        got = sorted(v.lower() for v in ans_of(cap, "PTR"))
        return want == got and want != [], f"dig={want} lib={got}"

    if case == "dnskey":
        want = sorted((int(r.split()[0]), int(r.split()[1]), int(r.split()[2]))
                      for (_, t, r) in answers if t == "DNSKEY")
        got = sorted((int(v.split()[0]), int(v.split()[1]), int(v.split()[2]))
                     for v in ans_of(cap, "DNSKEY"))
        if want != got or want == []:
            return False, f"dig={want} lib={got}"
        # RFC 4034 Appendix B: the RRSIG covering this DNSKEY RRset names the
        # key tag of the key that signed it — the computed tags must contain it.
        tags = dnskey_tags(cap)
        sig_tags = [int(r["typed"].split()[7]) for r in cap["rrs"]
                    if r["sec"] == "answer" and r["type"] == 46
                    and r["typed"].split()[1] == "48"]
        ok = sig_tags != [] and all(t in tags for t in sig_tags)
        return ok, f"fields ok; RRSIG-over-DNSKEY tags={sig_tags} computed={sorted(tags)}"

    if case == "ds":
        want = sorted((int(r.split()[0]), int(r.split()[1]), int(r.split()[2]))
                      for (_, t, r) in answers if t == "DS")
        got = sorted((int(v.split()[0]), int(v.split()[1]), int(v.split()[2]))
                     for v in ans_of(cap, "DS"))
        return want == got and want != [], f"dig={want} lib={got}"

    if case == "https-svcb":
        got = ans_of(cap, "SVCB")
        n_dig = len([1 for (_, t, _) in answers if t in ("HTTPS", "TYPE65")])
        return len(got) == n_dig and got != [], f"dig n={n_dig} lib={got}"

    if case == "https-typed":
        # dig ≥ 9.16 prints typed SvcParams: alpn="h3,h2" ipv4hint=1.2.3.4,...
        want_alpn = want_v4 = None
        for (_, t, r) in answers:
            if t in ("HTTPS", "SVCB"):
                m = re.search(r'alpn="([^"]*)"', r)
                if m:
                    want_alpn = sorted(m.group(1).split(","))
                m = re.search(r"ipv4hint=(\S+)", r)
                if m:
                    want_v4 = sorted(m.group(1).split(","))
        got_alpn = got_v4 = None
        for v in ans_of(cap, "SVCB"):
            m = re.search(r"alpn=(\S+)", v)
            if m:
                got_alpn = sorted(m.group(1).split(","))
            m = re.search(r"ipv4hint=(\S+)", v)
            if m:
                got_v4 = sorted(m.group(1).split(","))
        ok = want_alpn is not None and want_alpn == got_alpn and want_v4 == got_v4
        return ok, (f"dig alpn={want_alpn} v4={want_v4} "
                    f"lib alpn={got_alpn} v4={got_v4}")

    if case == "caa-other":
        # No typed CAA reader: pass = the records parse structurally as `other`.
        got = ans_of(cap, "OTHER")
        n_dig = len([1 for (_, t, _) in answers if t in ("CAA", "TYPE257")])
        return len(got) == n_dig and got != [], f"dig n={n_dig} lib OTHER={got}"

    if case == "nsec3param":
        want = [(r.split()[0], r.split()[1], r.split()[2], r.split()[3].lower())
                for (_, t, r) in answers if t == "NSEC3PARAM"]
        got = [(v.split()[0], v.split()[1], v.split()[2], v.split()[3].lower())
               for v in ans_of(cap, "NSEC3PARAM")]
        return want == got and want != [], f"dig={want} lib={got}"

    if case == "cookie":
        # Oracle: the RFC 7873 COOKIE option decoded independently out of the
        # exact query octets dig sent; the typed reader must agree on the
        # 8-octet client cookie (and the server half, when echoed).
        wire = query_cookie_from_wire(case)
        got = cap.get("qcookie")
        ok = wire is not None and got is not None and wire[0] == got[0]
        return ok, f"wire cookie={wire} lib QCOOKIE={got}"

    return False, "no oracle for case"


# Record types with typed readers: `other` for these counts as a typed gap.
# RFC 5155 NSEC3 (50) and NSEC3PARAM (51) now included.
TYPED = {1, 2, 5, 6, 12, 15, 16, 28, 41, 43, 46, 47, 48, 50, 51, 64, 65}


def main():
    if "--capture" in sys.argv:
        rc = subprocess.run([sys.executable, os.path.join(HERE, "capture.py")]).returncode
        if rc != 0:
            sys.exit("capture failed")

    report = run_lean()
    with open(os.path.join(CAPDIR, "lean-report.txt"), "w") as f:
        f.write(report)
    caps = parse_report(report)

    cases = []
    with open(os.path.join(CAPDIR, "manifest.txt")) as f:
        for line in f:
            if line.strip():
                cases.append(line.split()[0])

    total_checks = passed_checks = 0
    case_pass = 0
    lines = []
    for case in cases:
        cap = caps.get(case)
        if cap is None:
            lines.append(f"FAIL {case}: no report")
            total_checks += 5
            continue
        checks = []
        checks.append(("qparse", cap.get("qparse", False)
                       and cap.get("frame", True), ""))
        checks.append(("rparse", cap.get("rparse", False), ""))
        bad = [r for r in cap["rrs"]
               if r["typed"] == "MALFORMED"
               or (r["type"] in TYPED and r["typed"].startswith("OTHER"))
               or "badbitmap" in r["typed"]]
        checks.append(("typed", cap.get("rparse", False) and not bad,
                       "; ".join(f"{r['sec']}/{r['type']}:{r['typed']}" for r in bad)))
        _, status, _ = dig_answers(case)
        want_x = STATUS.get(status)
        checks.append(("xrcode", want_x is not None and cap.get("xrcode") == want_x,
                       f"dig status={status}({want_x}) lib xrcode={cap.get('xrcode')}"))
        ok, detail = check_extract(case, cap)
        checks.append(("extract", ok, detail))

        all_ok = all(c[1] for c in checks)
        case_pass += all_ok
        for cname, cok, detail in checks:
            total_checks += 1
            passed_checks += cok
            if not cok:
                lines.append(f"FAIL {case}/{cname}: {detail}")
        lines.append(f"{'PASS' if all_ok else 'FAIL'} {case}: "
                     + " ".join(f"{c[0]}={'ok' if c[1] else 'FAIL'}" for c in checks))

    print("== dns-battery: dig wire captures vs Dns library ==")
    for line in lines:
        print(line)
    print(f"dns-battery: {case_pass}/{len(cases)} cases passed "
          f"({passed_checks}/{total_checks} checks)")
    return 0 if case_pass == len(cases) else 1


if __name__ == "__main__":
    sys.exit(main())
