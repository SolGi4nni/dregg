#!/usr/bin/env python3
"""RFC 9111 (HTTP Caching) conformance battery for the deployed serve's cache path.

Drives the deployed `dataplane` binary with the response cache active
(DRORB_EFFECT_SEAM=1) over raw TCP and checks the cache lane against the
normative requirements of RFC 9111 (plus the cache-relevant clauses of
RFC 9110 it depends on: Vary, Date, 304 generation, conditional evaluation).

The cache under test is the serve's own response store: cacheable surface is a
range-free GET under /static (the proven key is `method SP target`, so a query
string mints a fresh cache entry — the battery keys every check off a unique
`?u=<nonce>` target to isolate state). A cache HIT is observable: the shell
stamps `X-Cache: HIT` and `Age: <seconds>` on a response replayed from the
store, so "served from cache without validation" is decidable from the wire.

Every check crafts real requests, reads real bytes, and derives PASS/FAIL from
the observed response — failures are the cache gap map, not harness errors.
Verdicts:
  PASS  observed behavior satisfies the cited requirement
  FAIL  observed behavior violates the cited requirement (MUST unless noted)
  INFO  behavior recorded; the RFC permits it or the clause is not observable
        from the wire (recorded for the gap map, not counted as pass/fail)

Run against a serve already listening:

    DRORB_RUST_GZIP=1 DRORB_EFFECT_SEAM=1 \
      ./target/release/dataplane --bind 127.0.0.1:8471 --no-udp --io blocking
    python3 conformance/rfc9111_caching.py    # table + results_rfc9111.json

Env: CONF_HTTP_PORT (default 8471), CONF_HTTP_HOST (default 127.0.0.1).
NOTE: includes freshness-expiry checks — the deployed lifetime is 60s, so the
battery sleeps past one lifetime and takes ~80s wall clock.
Exit code is always 0 — FAILs are findings.
"""
import json
import os
import socket
import sys
import time

HOST = os.environ.get("CONF_HTTP_HOST", "127.0.0.1")
PORT = int(os.environ.get("CONF_HTTP_PORT", "8471"))
LIFETIME = 60  # the deployed cache freshness lifetime (seconds)
RUN = format(int(time.time() * 1000) & 0xFFFFFFFF, "08x")  # per-run key nonce
RESULTS = []


# ---------------------------------------------------------------------------
# wire helpers
# ---------------------------------------------------------------------------
def raw(req, timeout=6.0, cap=1 << 20):
    """Send raw bytes on a fresh connection; return all bytes until close/timeout.
    None if the connection was refused (server down)."""
    try:
        s = socket.create_connection((HOST, PORT), timeout=timeout)
    except ConnectionRefusedError:
        return None
    s.settimeout(timeout)
    try:
        s.sendall(req)
        buf = b""
        while len(buf) < cap:
            try:
                d = s.recv(65536)
            except socket.timeout:
                break
            if not d:
                break
            buf += d
        return buf
    finally:
        s.close()


def get(target, extra=b"", method=b"GET"):
    """One request/response on a fresh connection (Connection: close)."""
    req = (method + b" " + target.encode() + b" HTTP/1.1\r\n"
           b"Host: conf\r\n" + extra + b"Connection: close\r\n\r\n")
    return raw(req)


def split_head(resp):
    head, _, body = (resp or b"").partition(b"\r\n\r\n")
    return head, body


def status_code(resp):
    parts = (resp or b"").split(b"\r\n", 1)[0].split(b" ", 2)
    if len(parts) >= 2 and parts[1].isdigit():
        return int(parts[1])
    return None


def header(head, name):
    """Value of the first header `name` (case-insensitive), or None."""
    for line in head.split(b"\r\n")[1:]:
        if line.lower().startswith(name.lower() + b":"):
            return line.split(b":", 1)[1].strip()
    return None


def is_hit(head):
    """Served from the store without running the handler (the shell's stamp)."""
    v = header(head, b"x-cache")
    return v is not None and v.upper() == b"HIT"


def age_of(head):
    v = header(head, b"age")
    if v is not None and v.isdigit():
        return int(v)
    return None


def key(tag):
    """A unique cacheable target for this check (fresh cache entry)."""
    return f"/static/app.js?u={RUN}-{tag}"


def prime(tag, extra=b""):
    """Fetch a fresh key once (populates the store); return (resp, target)."""
    t = key(tag)
    return get(t, extra), t


def record(cid, group, rfc, criterion, verdict, observed):
    RESULTS.append({"id": cid, "group": group, "rfc": rfc,
                    "criterion": criterion, "verdict": verdict,
                    "observed": observed})


GZ = b"\x1f\x8b"  # gzip magic


# ---------------------------------------------------------------------------
# Group A — storage & reuse of the stored response (RFC 9111 §3, §4)
# ---------------------------------------------------------------------------
def a_storage():
    r1, t = prime("a")
    h1, b1 = split_head(r1)
    r2 = get(t)
    h2, b2 = split_head(r2)

    record("A1-store-and-reuse", "storage", "9111 §3/§4",
           "a cacheable 200 (range-free GET) is stored and a repeat request is "
           "served from the store (X-Cache: HIT observability stamp)",
           "PASS" if (status_code(r1) == 200 and not is_hit(h1) and is_hit(h2))
           else "FAIL",
           f"first: {status_code(r1)} hit={is_hit(h1)}; "
           f"second: {status_code(r2)} hit={is_hit(h2)}")

    record("A2-reuse-identical-body", "storage", "9111 §4",
           "the reused response body is byte-identical to the stored response",
           "PASS" if (is_hit(h2) and b1 == b2) else "FAIL",
           f"stored {len(b1)}B, replayed {len(b2)}B, equal={b1 == b2}")

    record("A3-reuse-status", "storage", "9111 §4",
           "the reused response preserves the stored status code",
           "PASS" if status_code(r2) == 200 else "FAIL",
           f"replayed status {status_code(r2)}")

    same = all(header(h1, n) == header(h2, n)
               for n in (b"etag", b"content-type", b"accept-ranges"))
    record("A4-reuse-headers", "storage", "9111 §4/§3.2",
           "the reused response preserves the stored header fields "
           "(ETag, Content-Type, Accept-Ranges)",
           "PASS" if (is_hit(h2) and same) else "FAIL",
           f"etag {header(h1, b'etag')}=={header(h2, b'etag')}, "
           f"ct equal={header(h1, b'content-type') == header(h2, b'content-type')}")

    cl = header(h2, b"content-length")
    record("A5-reuse-framing", "storage", "9111 §4 (framing)",
           "Content-Length on the replayed response equals the replayed body size",
           "PASS" if (cl is not None and cl.isdigit() and int(cl) == len(b2))
           else "FAIL",
           f"Content-Length={cl!r}, body={len(b2)}B")

    # negative caching of an error response (allowed: 404 is heuristically
    # cacheable, RFC 9110 §15.1 / 9111 §4.2.2 — recorded for the gap map)
    t4 = f"/static/missing-{RUN}"
    r1 = get(t4)
    r2 = get(t4)
    h2, _ = split_head(r2)
    record("A6-404-negative-cache", "storage", "9111 §4.2.2 (heuristic)",
           "is an error response (404) stored and reused? (permitted for 404 "
           "via heuristic freshness; recorded, not judged)",
           "INFO",
           f"first={status_code(r1)}, repeat={status_code(r2)} hit={is_hit(h2)}")


# ---------------------------------------------------------------------------
# Group B — Age and Date (RFC 9111 §4.2.3, §5.1; RFC 9110 §6.6.1)
# ---------------------------------------------------------------------------
def b_age():
    r1, t = prime("b")
    h1, _ = split_head(r1)

    record("B1-age-absent-from-origin", "age", "9111 §5.1",
           "a response generated by the origin for this request does not carry "
           "Age (its presence implies cache replay)",
           "PASS" if age_of(h1) is None else "FAIL",
           f"miss response Age={header(h1, b'age')!r}")

    r2 = get(t)
    h2, _ = split_head(r2)
    record("B2-age-present-on-reuse", "age", "9111 §4 / §5.1",
           "when a stored response is used without validation the cache MUST "
           "generate an Age header field",
           "PASS" if (is_hit(h2) and age_of(h2) is not None) else "FAIL",
           f"hit={is_hit(h2)} Age={header(h2, b'age')!r}")

    v = header(h2, b"age")
    record("B3-age-syntax", "age", "9111 §5.1",
           "Age is a non-negative delta-seconds integer",
           "PASS" if (v is not None and v.isdigit()) else "FAIL",
           f"Age={v!r}")

    time.sleep(3)
    r3 = get(t)
    h3, _ = split_head(r3)
    a3 = age_of(h3)
    record("B4-age-advances", "age", "9111 §4.2.3",
           "current_age grows with resident time: ~3s after storage the "
           "replayed Age is in [2..6]",
           "PASS" if (is_hit(h3) and a3 is not None and 2 <= a3 <= 6) else "FAIL",
           f"hit={is_hit(h3)} Age={a3} after 3s")

    record("B5-date-header", "age", "9110 §6.6.1 (9111 §4.2.3 depends on it)",
           "an origin with a clock MUST generate Date; a downstream cache "
           "cannot compute apparent_age without it",
           "PASS" if header(h1, b"date") is not None else "FAIL",
           f"Date on 200: {header(h1, b'date')!r}")


# ---------------------------------------------------------------------------
# Group C — request cache directives (RFC 9111 §5.2.1, §5.4)
# ---------------------------------------------------------------------------
def c_request_directives():
    # C1 no-store: the response to this request MUST NOT be stored
    _, t = prime("c1", extra=b"Cache-Control: no-store\r\n")
    r2 = get(t)
    h2, _ = split_head(r2)
    record("C1-req-no-store", "req-directives", "9111 §5.2.1.5",
           "a cache MUST NOT store any part of a request carrying "
           "Cache-Control: no-store, or of its response",
           "FAIL" if is_hit(h2) else "PASS",
           f"plain follow-up hit={is_hit(h2)} (stored despite no-store)"
           if is_hit(h2) else "follow-up was not served from the store")

    # C2 no-cache: MUST NOT use a stored response without successful validation
    _, t = prime("c2")
    get(t)  # confirm stored
    r = get(t, extra=b"Cache-Control: no-cache\r\n")
    h, _ = split_head(r)
    record("C2-req-no-cache", "req-directives", "9111 §5.2.1.4",
           "a cache MUST NOT use a stored response to satisfy a request with "
           "Cache-Control: no-cache without successful validation on the origin",
           "FAIL" if is_hit(h) else "PASS",
           f"hit={is_hit(h)} Age={header(h, b'age')!r} (replayed unvalidated)"
           if is_hit(h) else "not replayed from the store")

    # C3 max-age=0
    _, t = prime("c3")
    get(t)
    r = get(t, extra=b"Cache-Control: max-age=0\r\n")
    h, _ = split_head(r)
    record("C3-req-max-age-0", "req-directives", "9111 §5.2.1.1",
           "max-age=0: the client is unwilling to accept any stored response "
           "unless validated (equivalent to no-cache)",
           "FAIL" if is_hit(h) else "PASS",
           f"hit={is_hit(h)} Age={header(h, b'age')!r}")

    # C4 max-age=1 with an older entry
    _, t = prime("c4")
    time.sleep(2.5)
    r = get(t, extra=b"Cache-Control: max-age=1\r\n")
    h, _ = split_head(r)
    a = age_of(h)
    record("C4-req-max-age-bound", "req-directives", "9111 §5.2.1.1",
           "a stored response whose current_age exceeds the request max-age "
           "MUST NOT be used to satisfy it",
           "FAIL" if (is_hit(h) and a is not None and a > 1) else "PASS",
           f"hit={is_hit(h)} Age={a} vs request max-age=1")

    # C5 min-fresh larger than any possible remaining freshness
    _, t = prime("c5")
    r = get(t, extra=b"Cache-Control: min-fresh=3600\r\n")
    h, _ = split_head(r)
    record("C5-req-min-fresh", "req-directives", "9111 §5.2.1.3",
           "min-fresh=3600: the client wants a response still fresh in 3600s; "
           f"the deployed lifetime is {LIFETIME}s, so no stored response qualifies",
           "FAIL" if is_hit(h) else "PASS",
           f"hit={is_hit(h)} Age={header(h, b'age')!r}")

    # C6 only-if-cached on a cold key -> 504
    t = key("c6")
    r = get(t, extra=b"Cache-Control: only-if-cached\r\n")
    record("C6-only-if-cached-cold", "req-directives", "9111 §5.2.1.7",
           "only-if-cached: a cache that cannot satisfy the request from its "
           "store MUST respond 504 (Gateway Timeout), not contact the origin",
           "PASS" if status_code(r) == 504 else "FAIL",
           f"status={status_code(r)} (origin was consulted)"
           if status_code(r) != 504 else "504 as required")

    # C7 only-if-cached on a warm key -> served from store (or 504)
    _, t = prime("c7")
    get(t)
    r = get(t, extra=b"Cache-Control: only-if-cached\r\n")
    h, _ = split_head(r)
    record("C7-only-if-cached-warm", "req-directives", "9111 §5.2.1.7",
           "only-if-cached on a stored-fresh entry: reply using the stored "
           "response (or 504); forwarding to the origin is the one forbidden path",
           "PASS" if (is_hit(h) or status_code(r) == 504) else "FAIL",
           f"hit={is_hit(h)} status={status_code(r)}")

    # C8 Pragma: no-cache (SHOULD-level backward compat)
    _, t = prime("c8")
    get(t)
    r = get(t, extra=b"Pragma: no-cache\r\n")
    h, _ = split_head(r)
    record("C8-pragma-no-cache", "req-directives", "9111 §5.4 (SHOULD)",
           "Pragma: no-cache on a request without Cache-Control SHOULD be "
           "treated as Cache-Control: no-cache",
           "FAIL" if is_hit(h) else "PASS",
           f"hit={is_hit(h)} Age={header(h, b'age')!r}")


# ---------------------------------------------------------------------------
# Group D — response directives (RFC 9111 §5.2.2) — observability note
# ---------------------------------------------------------------------------
def d_response_directives():
    r, _ = prime("d1")
    h, _ = split_head(r)
    cc = header(h, b"cache-control")
    exp = header(h, b"expires")
    record("D1-explicit-freshness", "resp-directives", "9111 §4.2.1/§4.2.2",
           "does the origin advertise explicit freshness (Cache-Control/"
           "Expires) on the cacheable 200? absent means every downstream "
           "cache falls back to heuristics while this cache uses an internal "
           f"{LIFETIME}s lifetime the response never names",
           "INFO",
           f"Cache-Control={cc!r} Expires={exp!r}")

    record("D2-resp-directives-unenforceable", "resp-directives",
           "9111 §5.2.2.1/.3/.5/.7/.10",
           "response no-store/private/max-age/s-maxage/must-revalidate cannot "
           "be exercised from the wire: the origin emits no Cache-Control and "
           "the store applies a constant lifetime independent of response "
           "directives — the honoring path is untestable (and unimplemented)",
           "INFO",
           "store lifetime is the proven constant; response directives are "
           "not consulted at store time")


# ---------------------------------------------------------------------------
# Group E — Vary and secondary cache keys (RFC 9111 §4.1; RFC 9110 §12.5.5)
# ---------------------------------------------------------------------------
def e_vary():
    # the origin negotiates on Accept-Encoding (gzip seam), so Vary matters
    r1, t = prime("e1", extra=b"Accept-Encoding: gzip\r\n")
    h1, b1 = split_head(r1)
    gz_negotiated = header(h1, b"content-encoding") == b"gzip"

    record("E1-vary-emitted", "vary", "9110 §12.5.5 (SHOULD)",
           "an origin that varies the representation on Accept-Encoding "
           "SHOULD send Vary: Accept-Encoding on the response",
           "INFO" if not gz_negotiated else
           ("PASS" if header(h1, b"vary") is not None else "FAIL"),
           f"negotiated gzip={gz_negotiated}, Vary={header(h1, b'vary')!r}")

    # E2: the poisoning direction — a client that did NOT offer gzip must not
    # be handed the stored gzip variant
    r2 = get(t)  # no Accept-Encoding
    h2, b2 = split_head(r2)
    poisoned = is_hit(h2) and (b2.startswith(GZ)
                               or header(h2, b"content-encoding") == b"gzip")
    record("E2-vary-secondary-key", "vary", "9111 §4.1",
           "a stored response with a selecting header (content-coding chosen "
           "by Accept-Encoding) MUST NOT be reused for a request whose "
           "selecting header does not match: the cache key must incorporate "
           "the Vary dimension",
           "FAIL" if poisoned else "PASS",
           f"hit={is_hit(h2)} Content-Encoding={header(h2, b'content-encoding')!r} "
           f"body-is-gzip={b2.startswith(GZ)} (gzip variant served to a client "
           "that never offered gzip)" if poisoned else
           f"hit={is_hit(h2)} body-is-gzip={b2.startswith(GZ)}")

    # E3: reverse direction — identity stored, gzip-capable client: identity
    # is always acceptable, so a HIT here is fine; the body must be usable
    r1, t = prime("e3")  # identity
    r2 = get(t, extra=b"Accept-Encoding: gzip\r\n")
    h2, b2 = split_head(r2)
    record("E3-identity-acceptable", "vary", "9111 §4.1 / 9110 §12.5.3",
           "serving the stored identity variant to a gzip-capable client is "
           "permitted (identity is always acceptable); the body must not be "
           "mislabeled",
           "PASS" if (not b2.startswith(GZ)
                      and header(h2, b"content-encoding") != b"gzip") else "FAIL",
           f"hit={is_hit(h2)} Content-Encoding={header(h2, b'content-encoding')!r} "
           f"body-is-gzip={b2.startswith(GZ)}")


# ---------------------------------------------------------------------------
# Group F — validation on the cache path (RFC 9111 §4.3; RFC 9110 §13, §15.4.5)
# ---------------------------------------------------------------------------
def f_conditional():
    r1, t = prime("f")
    h1, _ = split_head(r1)
    etag = header(h1, b"etag")
    get(t)  # ensure stored

    r = get(t, extra=b"If-None-Match: " + (etag or b'"x"') + b"\r\n")
    h, b = split_head(r)
    record("F1-inm-304", "conditional", "9111 §4.3.2 / 9110 §13.1.2",
           "If-None-Match matching the stored ETag is answered 304 from the "
           "cache path",
           "PASS" if status_code(r) == 304 else "FAIL",
           f"status={status_code(r)} for INM {etag!r}")

    record("F2-304-empty-body", "conditional", "9110 §15.4.5",
           "a 304 response has no content",
           "PASS" if (status_code(r) == 304 and b == b"") else "FAIL",
           f"status={status_code(r)} body={len(b)}B")

    record("F3-304-etag", "conditional", "9110 §15.4.5",
           "a 304 carries the header fields (ETag) that would have been sent "
           "in the 200",
           "PASS" if (status_code(r) == 304 and header(h, b"etag") == etag)
           else "FAIL",
           f"304 ETag={header(h, b'etag')!r} vs stored {etag!r}")

    r = get(t, extra=b'If-None-Match: "no-such-etag"\r\n')
    h, b = split_head(r)
    record("F4-inm-mismatch-200", "conditional", "9110 §13.1.2",
           "If-None-Match not matching is answered with the full 200",
           "PASS" if (status_code(r) == 200 and len(b) > 0) else "FAIL",
           f"status={status_code(r)} body={len(b)}B")

    r = get(t, extra=b'If-Match: "no-such-etag"\r\n')
    record("F5-if-match-412", "conditional", "9110 §13.1.1",
           "If-Match not matching the selected representation is answered 412",
           "PASS" if status_code(r) == 412 else "FAIL",
           f"status={status_code(r)}")


# ---------------------------------------------------------------------------
# Group G — method scoping, Range, invalidation (RFC 9111 §3, §4.4; 9110 §14)
# ---------------------------------------------------------------------------
def g_methods():
    # G1: HEAD does not collide with GET in the key
    t = key("g1")
    get(t, method=b"HEAD")
    r = get(t)
    h, b = split_head(r)
    record("G1-head-get-distinct", "methods", "9111 §4 (key includes method)",
           "a HEAD response is not replayed for a GET (the GET body is full)",
           "PASS" if (status_code(r) == 200 and len(b) > 0) else "FAIL",
           f"GET after HEAD: status={status_code(r)} body={len(b)}B hit={is_hit(h)}")

    # G2: POST responses are not cached
    t = key("g2")
    r1 = get(t, method=b"POST")
    r2 = get(t, method=b"POST")
    h2, _ = split_head(r2)
    record("G2-post-not-stored", "methods", "9111 §3 (method cacheability)",
           "a POST response is not stored/replayed (POST is not cacheable "
           "here — no explicit freshness)",
           "FAIL" if is_hit(h2) else "PASS",
           f"POST status={status_code(r1)}; repeat hit={is_hit(h2)}")

    # G3: unsafe method invalidates the stored GET response
    _, t = prime("g3")
    r_hit = get(t)
    hh, _ = split_head(r_hit)
    rp = get(t, method=b"POST")
    post_status = status_code(rp)
    r_after = get(t)
    ha, _ = split_head(r_after)
    if post_status is not None and post_status < 400:
        verdict = "FAIL" if is_hit(ha) else "PASS"
        obs = (f"POST answered {post_status} (non-error) and the pre-POST "
               f"entry was {'still replayed' if is_hit(ha) else 'invalidated'} "
               f"(hit={is_hit(ha)}, Age={header(ha, b'age')!r})")
    else:
        verdict = "INFO"
        obs = f"POST answered {post_status} (error) — invalidation not required"
    record("G3-unsafe-invalidates", "invalidation", "9111 §4.4",
           "a cache MUST invalidate the target URI when it receives a "
           "non-error response to an unsafe method (POST)",
           verdict, obs)

    # G4: a Range request is not answered with the full stored 200
    _, t = prime("g4")
    get(t)  # stored + hot
    r = get(t, extra=b"Range: bytes=0-3\r\n")
    h, b = split_head(r)
    record("G4-range-not-replayed-full", "range", "9111 §3.3-adjacent / 9110 §14",
           "a ranged GET on a hot cache entry is answered 206 with the "
           "requested part, not the stored full 200",
           "PASS" if (status_code(r) == 206 and len(b) == 4) else "FAIL",
           f"status={status_code(r)} body={len(b)}B hit={is_hit(h)}")

    # G5: a 206 is not stored as the full representation
    t = key("g5")
    get(t, extra=b"Range: bytes=0-3\r\n")  # cold key, partial first
    r = get(t)
    h, b = split_head(r)
    full = status_code(r) == 200 and len(b) > 4
    record("G5-partial-not-stored-as-full", "range", "9111 §3.3",
           "a cache MUST NOT reuse a stored partial (206) response to satisfy "
           "a request for the full representation",
           "PASS" if full else "FAIL",
           f"plain GET after ranged: status={status_code(r)} body={len(b)}B "
           f"hit={is_hit(h)}")

    # G6: the query string is part of the key
    _, t = prime("g6")
    get(t)
    r = get(t + "x")  # different target
    h, _ = split_head(r)
    record("G6-target-exact-key", "methods", "9111 §4.1 (URI match)",
           "a stored response is reused only for an identical target URI "
           "(distinct query strings are distinct entries)",
           "FAIL" if is_hit(h) else "PASS",
           f"different-target request hit={is_hit(h)}")


# ---------------------------------------------------------------------------
# Group H — Authorization (RFC 9111 §3.5)
# ---------------------------------------------------------------------------
def h_authorization():
    _, t = prime("h1", extra=b"Authorization: Bearer conf-token\r\n")
    r2 = get(t)
    h2, _ = split_head(r2)
    record("H1-authorized-not-stored", "authorization", "9111 §3.5",
           "a shared cache MUST NOT store the response to a request with an "
           "Authorization field unless the response explicitly allows it "
           "(public / must-revalidate / s-maxage) — this response carries "
           "no such directive",
           "FAIL" if is_hit(h2) else "PASS",
           f"unauthenticated follow-up hit={is_hit(h2)}"
           + (" (authorized response replayed to an unauthenticated client)"
              if is_hit(h2) else ""))


# ---------------------------------------------------------------------------
# Group I — freshness lifetime and staleness (RFC 9111 §4.2, §5.2.2.2)
# ---------------------------------------------------------------------------
def i_expiry(t_primed, primed_at):
    # I1: fresh within the lifetime (already implied by B4 but assert bound)
    r = get(t_primed)
    h, _ = split_head(r)
    a = age_of(h)
    record("I1-fresh-window-served", "freshness", "9111 §4.2",
           f"within the {LIFETIME}s lifetime the stored response is reusable "
           "and Age never exceeds the lifetime",
           "PASS" if (is_hit(h) and a is not None and a <= LIFETIME) else "FAIL",
           f"hit={is_hit(h)} Age={a} at t+{time.time() - primed_at:.0f}s")

    # sleep past the lifetime
    remaining = LIFETIME + 3 - (time.time() - primed_at)
    if remaining > 0:
        print(f"  [expiry] sleeping {remaining:.0f}s past the {LIFETIME}s "
              "lifetime …", flush=True)
        time.sleep(remaining)

    r = get(t_primed)
    h, _ = split_head(r)
    a = age_of(h)
    stale_served = is_hit(h) and a is not None and a > LIFETIME
    record("I2-stale-not-served", "freshness", "9111 §4.2.4 / §5.2.2.2",
           "a response past its freshness lifetime MUST NOT be served from "
           "the store without validation (no stale replay)",
           "FAIL" if stale_served else "PASS",
           f"t+{time.time() - primed_at:.0f}s: hit={is_hit(h)} Age={a}")

    r = get(t_primed)
    h, _ = split_head(r)
    a = age_of(h)
    record("I3-re-prime-after-expiry", "freshness", "9111 §3",
           "after expiry the next origin response is stored again (the cache "
           "recovers; follow-up is a fresh replay with small Age)",
           "PASS" if (is_hit(h) and a is not None and a <= 5) else "FAIL",
           f"hit={is_hit(h)} Age={a}")

    record("I4-no-warning", "freshness", "9111 §5.5",
           "the Warning field is deprecated: a cache SHOULD NOT generate it",
           "PASS" if header(h, b"warning") is None else "FAIL",
           f"Warning={header(h, b'warning')!r}")


# ---------------------------------------------------------------------------
def main():
    r = get("/static/app.js")
    if r is None:
        print(f"server not listening on {HOST}:{PORT}", file=sys.stderr)
        sys.exit(2)

    # prime the expiry key FIRST so the lifetime clock runs during the battery
    r1, t_exp = prime("expiry")
    primed_at = time.time()
    if status_code(r1) != 200:
        print(f"expiry prime got {status_code(r1)}", file=sys.stderr)

    a_storage()
    b_age()
    c_request_directives()
    d_response_directives()
    e_vary()
    f_conditional()
    g_methods()
    h_authorization()
    i_expiry(t_exp, primed_at)

    # table
    w = max(len(x["id"]) for x in RESULTS)
    counts = {"PASS": 0, "FAIL": 0, "INFO": 0}
    for x in RESULTS:
        counts[x["verdict"]] += 1
        print(f"{x['verdict']:4}  {x['id']:{w}}  [{x['rfc']}]  {x['observed']}")
    judged = counts["PASS"] + counts["FAIL"]
    print(f"\nRFC 9111 cache battery: {counts['PASS']}/{judged} judged checks "
          f"pass ({counts['FAIL']} FAIL, {counts['INFO']} INFO, "
          f"{len(RESULTS)} total)")

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "results_rfc9111.json")
    with open(out, "w") as f:
        json.dump({"host": HOST, "port": PORT, "run": RUN,
                   "pass": counts["PASS"], "fail": counts["FAIL"],
                   "info": counts["INFO"], "results": RESULTS}, f, indent=1)
    print(f"results written to {out}")


if __name__ == "__main__":
    main()
