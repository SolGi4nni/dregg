# drorb — a formally verified network engine, in Lean 4

A reverse-proxy / edge server whose behaviour is stated and proved as theorems,
machine-checked by the Lean 4 kernel, and driven — over real sockets — by an
untrusted IO shell that never touches the proven core.

Most fast network stacks ask for your trust: they parse your traffic, terminate
your TLS, route your requests, and you take their word that they did what they
said. `drorb` hands you a proof instead. Every property below is a theorem the
kernel accepts, or it does not ship.

## What is proven

- **The wire.** HTTP/1.1, HTTP/2 (framing · HPACK · streams), HTTP/3 + QPACK,
  QUIC, TLS 1.3, WebSocket, DNS parsing, SSE, 103 Early Hints — each as a total
  transition system with safety theorems (well-formedness, framing, in-bounds,
  termination). For the HTTP/1.1 parser the safety claim is upgraded to
  **correctness**: the request-line and header fields resolve to *exactly* their
  input bytes (`ArenaSound`, `HeaderSound`) — not just in-bounds, but *right*. The
  same soundness is proved for the HPACK/QPACK **literal, non-Huffman** field case
  (`H2Sound`, `QpackSound`); Huffman coding and the dynamic table are modelled as
  boundaries, not yet proved. Most lanes are safety-only so far — the
  safety→correctness upgrade is ongoing, not finished.
- **The fabric.** Routing (path traversal is *impossible*, not filtered), load
  balancing, health checks, upstream pools, timeouts, circuit breakers, rate
  limiting, sticky sessions, SOCKS egress, graceful drain, body streaming,
  header rewrite, a streaming HTML rewriter (chunk-boundary-safe), a response
  cache with request coalescing.
- **The vault.** The served surface *is* the declared surface; per-tenant
  isolation; a diagnostic tap that leaks nothing when disabled; mTLS; ACME;
  Certificate Transparency; the JWT algorithm-confusion vulnerability *proven
  absent*. TLS 1.3 and QUIC key schedules + AEAD packet protection run over
  **verified crypto** (HACL\*/EverCrypt) — the assumed properties are theorems
  proved upstream, not hand-waved.
- **The floor.** An `io_uring`-style submission/completion ring modelled as a
  two-player LTS: every buffer the kernel lends is recycled *exactly once*, under
  every demonic interleaving, including ones no test would reach. A refinement
  onto the seL4 sDDF ring for the microkernel substrate.
- **The pipeline.** The deployed serve is a modular fold over a `Stage` list —
  each feature (auth gate, IP filter, rate limit, CORS, HSTS, gzip, …) is an
  independently-verified stage whose byte-effect on the emitted response is its
  own theorem. Adding a feature is one file.

## What runs

A single request in, a response out, over a real socket:

```
GET /health          → 200, with HSTS + security headers (proven stages)
GET /admin           → 401 (the real JWT gate short-circuits)
GET /..%2fetc/passwd → 404 (a literal ../ escaping the root is blocked, not filtered)
```

Native IO drivers (macOS `kqueue`/BSD sockets today; Linux `io_uring`/`epoll`,
seL4 Microkit, and Windows IOCP scaffolded) run the *unchanged* proven core.
WebSocket round-trips over TCP. A QUIC Initial packet in the ChaCha20-Poly1305
suite is decrypted via verified EverCrypt over a real UDP socket and reaches the
proven HTTP/3 dispatch (cross-checked against an off-the-shelf client). Full QUIC
agility needs AES-128-GCM, which EverCrypt only accelerates on x86; on other
targets an AES backend is dispatched to (see the crypto notes) — so on this host
the demonstrated suite is ChaCha20, not the full cipher set.

## The trust boundary, stated honestly

The theorems are about the models. Two things are trusted, named out loud:

1. **The Lean kernel** (and, for the compiled path, the HOL4 kernel + the
   CakeML/Pancake backend theorem + the crypto assumptions HACL\*/EverCrypt
   discharges). These are small, audited, published.
2. **The IO shell** — the socket, accept loop, and connection lifecycle. It is
   the untrusted environment; the proven core is the sacred part it drives. The
   shell is validated by testing; everything above it is proved.

The path from the Lean model to machine code with `leanc` out of the trusted
base is **early and open**. Small first-order kernels — a bounds check, a
saturating counter, a request-line byte scan and its composition — are emitted to
Pancake and proved to refine their Lean specifications against the real Pancake
semantics, kernel-checked with a clean axiom footprint. That establishes the
loop-and-refinement *technique* on straight-line/`While` code over a flat buffer.

It does **not** yet reach the engine's real shape. The models use algebraic
datatypes, allocating recursion, lists, and higher-order composition; Pancake is
first-order with manual memory and no allocator, no closures, no datatypes. So
emitting the whole engine requires building (and verifying) a data-layout
encoding, a recursion/stack story, and — the hard one — heap allocation with a
verified memory-management story. Those are substantial open problems, not a
mechanical repeat of the byte-scan proofs. Treat the compiled-hot-path claim as a
demonstrated technique on the easy fragment, with the general case unsolved.

## We audit ourselves

Verification is only worth what its statements say. Every wave of this work was
adversarially audited — reviewers pointed at its own claims to find where they
were weaker than advertised, and the findings (safety mistaken for correctness, a
vacuous theorem, an unwired lane) were fixed before the work landed. If a
theorem's name over-promises relative to its statement, that is a bug, and we
hunt it. `#print axioms` on the headline theorems shows only the core kernel
axioms (`propext`, `Quot.sound`, `Classical.choice`) plus the named crypto
assumptions — no `sorry`, anywhere.

## Building & running the server

Prerequisites: Lean 4 (`v4.17.0`, fetched by `elan` via `lean-toolchain`), Rust +
`cargo`, and the F\*-verified HACL\*/EverCrypt crypto backend (build
[hacl-star](https://github.com/hacl-star/hacl-star), point `HACL_DIST` at its
`dist/gcc-compatible`). macOS or Linux.

```sh
export HACL_DIST=/path/to/hacl-star/dist/gcc-compatible
./build.sh                                          # -> target/release/dataplane
DRORB_CONFIG=./sample.cfg ./target/release/dataplane 127.0.0.1:8080
curl http://127.0.0.1:8080/health                   # -> 200 ok
```

`build.sh` builds the FFI shims, compiles the proven serve to `libdrorb.a`, and links
the native dataplane. **The first build cold-compiles the Lean serve core — tens of
minutes;** rebuilds are incremental. The full operator guide (config grammar, vhosts,
proxy, TLS certs, live reload, metrics, systemd) is in
[`deploy/README.md`](./deploy/README.md).

To build **and re-check every proof**, run a full `lake build` (core Lean, no Mathlib;
slower — it elaborates every theorem). That path also links the Lean-built
executables, whose `lakefile.toml` stanzas assume `/opt/hacl-star` — symlink it, or set
`LIBRARY_PATH=$HACL_DIST` (which `build.sh` does). The verified-compiler probes ship
separately in the companion `orb-compiler/` drop.

## Licence

AGPL-3.0. A liberated, verifiable floor anyone can build on.
