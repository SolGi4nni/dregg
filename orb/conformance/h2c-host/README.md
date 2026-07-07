# h2c-host — interactive conformance host for the verified HTTP/2 engine

A minimal C shim that serves the verified HTTP/2 connection engine
(`H2/Conn.lean`, exported through `Reactor/H2Ingress.lean` as
`drorb_h2c_conn_init` / `drorb_h2c_conn_feed`) interactively over TCP: one
engine state per accepted connection, threaded across socket reads. Every
protocol decision — preface validation, frame walking, HPACK with the real
decode-side dynamic table, the per-stream FSM, SETTINGS/PING acknowledgement,
flow-control pacing, GOAWAY/RST_STREAM emission — happens inside the Lean
engine; the shim only moves bytes and closes cleanly (shutdown + drain, so the
peer sees FIN, never RST).

The process forks per connection so one idling connection cannot
head-of-line-block the accept loop — a conformance battery opens each test's
connection while the previous one may still be draining.

## Build and run

```sh
ffi/build-dataplane-lib.sh        # lake build Dataplane:static → libdrorb.a
conformance/h2c-host/build.sh     # link the host
conformance/h2c-host/h2c-host 18081
```

## Battery

```sh
h2spec -h 127.0.0.1 -p 18081
```

Result (h2spec 2.6.0, all suites, cleartext h2c):

```
146 tests, 145 passed, 1 skipped, 0 failed
```

The single skip is h2spec's TLS-dependent check, inapplicable on a cleartext
run.

## Hosting the engine inside the dataplane

This feed loop is the reference for replacing the dataplane's one-shot h2c
path (`crates/dataplane/src/blocking.rs`): the one-shot path answers only the
opening burst and closes, so SETTINGS synchronization, PING liveness, and
WINDOW_UPDATE-paced bodies — everything after the client's first flight —
never reach the engine. An interactive host threads
`drorb_h2c_conn_init`/`drorb_h2c_conn_feed` across reads exactly as
`serve_conn` here does. In the dataplane the Lean crossings must stay on the
runtime-owner thread: route the per-chunk feed through the serve gateway
(a seam variant carrying the opaque engine state, or a serve-thread-side
state table keyed by connection), then write the returned octets and close
cleanly when the engine raises its close flag (octet 0 of the returned
buffer), draining unread input before `close(2)` so the teardown is FIN, not
RST.
