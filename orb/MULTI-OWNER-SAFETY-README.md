# `DRORB_SERVE_OWNERS` — runtime-safety analysis + byte-identity evidence

The multi-owner lever (default-OFF) attaches `k-1` extra owner threads to the ONE
process-global Lean runtime (`serve.rs::spawn_attached_owner`, registered via
`lean_initialize_thread`), each with its own job channel; the blocking host pins
connections round-robin, the io_uring host pins shards. It was committed dormant
with its safety when ENABLED explicitly unverified. This document is that
verification: (1) the runtime-model analysis of why k threads may concurrently
cross the pure byte-serve exports, with each premise checked against the actual
toolchain sources and this tree's generated code; (2) my-hand byte-identity +
crash-safety evidence under real cross-owner concurrency; (3) the honest bounds —
what this does NOT establish.

## 1. The runtime threading model (toolchain v4.17.0, `LEAN_SMALL_ALLOCATOR`)

**Thread registration is exactly the runtime's own worker discipline.**
`lean_initialize_thread()` is `init_thread_heap()` (runtime `thread.cpp:52-56`),
and the runtime's own `thread_main` — the entry every runtime-spawned thread
(including task-pool workers) runs — calls the very same function first
(`thread.cpp:63-72`). An attached owner that registers before its first crossing
is therefore in the identical thread-local state as a runtime worker; running
pure code on many such threads concurrently is the runtime's normal
multi-threaded regime, not an off-label use. Under `LEAN_SMALL_ALLOCATOR`
(confirmed in this toolchain's `include/lean/config.h`) registration is
REQUIRED: `lean_alloc_small` dereferences the thread-local heap unconditionally,
so an unregistered thread crashes on its first allocation — the lever's
`spawn_attached_owner` registers before releasing the ready handshake.

**The reference-count protocol and its one invariant.** An object's `m_rc`
encodes single-threaded (`>0`, non-atomic inc/dec), multi-threaded (`<0`,
atomic), or persistent (`==0`, inc/dec are no-ops) — `lean.h:416-467`. The only
way k crossing threads can race is two threads doing non-atomic RC ops on the
SAME single-threaded object. So the safety obligation is exactly:

> no single-threaded (`m_rc > 0`) Lean object is ever reachable from two owner
> threads.

Discharged for this tree, premise by premise:

- **Everything shared between owners is a persistent module global.** Audit of
  ALL 538 generated `.c` files in `.lake/build/ir`: 27,131 object-typed global
  initializations in the module-init functions; 26,891 are immediately
  `lean_mark_persistent`-ed and the remaining 240 are scalar-typed globals
  (`uint8_t`/`size_t`/`double`) that carry no RC — **zero unmarked
  `lean_object*` globals** (audit script: re-run the grep/regex pass after any
  toolchain bump). `lean_mark_persistent` is deep (runtime `object.cpp:454`):
  it freezes the entire reachable graph — ctor fields, closure captures,
  arrays, thunk closures AND values, refs.
- **Per-call objects never leave their owner thread.** Every serve crossing
  (`serve.rs::serve_into` and the metered/cfg/braided variants) allocates the
  input `ByteArray` on the calling owner thread, the export consumes it, and
  the response object's bytes are copied into a host buffer before `lean_dec`
  — create, consume, copy-out, drop, all on one thread. Responses cross back
  to IO threads as plain host bytes, never as Lean objects.
- **The resumable/effect seams thread state as BYTES.** `interp.rs`
  (`frame_step`/`frame_resume`) serializes the continuation state into the next
  request's framing; no `lean_object*` is held across the channel. (This was
  already the single-owner design; the lever inherits it.)
- **The exports are pure.** Every `@[export drorb_serve*]` in `Dataplane.lean`
  is `ByteArray → ByteArray` (or `(peer, seq, input) → ByteArray`): no `IO`, no
  `ST`, no `Ref`. The one `lean_st_mk_ref` user in the generated tree
  (`IoQuic.c`) creates per-call ST refs and is not in `initialize_Dataplane`'s
  closure at all.
- **The C shim is stateless.** `ffi/drorb_ffi.c` is 36 lines of re-exported
  header inlines; no static mutable state. The verified-crypto dispatch is
  populated once at load and read-only afterwards.
- **The one lazy mutation reachable from persistent globals is MT-safe.**
  Thunk forcing (`object.cpp::lean_thunk_get_core`) atomically exchanges the
  closure, marks the computed value multi-threaded BEFORE publishing it, and
  makes racing threads spin-wait on the published value.
- **Even accidental cross-thread frees are designed for.** The small allocator
  keeps per-thread heaps; freeing an object whose page belongs to another heap
  routes it to that heap's import list under a mutex (`alloc.cpp:221-269`) —
  so an object dropped on a different thread than it was allocated on (e.g. a
  gateway send that never got drained) deallocates correctly.

**Wiring constraints the argument depends on (and the tree obeys):** TLS
connection jobs, UDP/datagram, admin, and reconfig crossings all ride the
PRIMARY gateway only — `main.rs` clones the owner-0 gateway for those paths
before the IO host builds the owner set, and the hosts shard only connection
byte-serve traffic across attached owners. Per-connection (blocking) /
per-shard (io_uring) pinning preserves request/response FIFO per connection.

## 2. My-hand evidence (this box, Linux io_uring + blocking hosts)

Probe: `conformance/owners_identity.py`. A 7-request pipelined corpus (1 MiB
`/bulk`, `/health`, `/` 404, unknown-path 404, `HEAD /bulk`, conditional
`GET /bulk` + `If-None-Match`, closing `/health`) is sent per fresh connection
and the ENTIRE response stream read to EOF is compared byte-for-byte against a
single-owner baseline — any interleaving, corruption, reordering, or truncation
anywhere is a mismatch. (Honest corpus note: the deployed default emits no
`ETag`, so the conditional arm answers 200, not a genuine 304.)

Baselines: time-invariant (two captures 1.5 s apart, `cmp` equal — the serve is
pure, no clock-dependent byte) and io-mode-invariant (uring baseline `cmp`-equal
to blocking baseline, 2,099,305 bytes).

| Config | Load | Result |
|---|---|---|
| uring, owners=4 | 32 thr × 100 conns (22,400 reqs, 6.7 GB) | every stream byte-identical, 0 failures |
| uring, owners=4 | ab -c 64 -n 20,000 `/bulk` (fresh conns) | 20,000 complete, **0 failed** |
| uring, owners=4 | ab -k -c 64 `/bulk` (20,000) + `/health` (50,000) | non-2xx = per-conn rate-gate arithmetic (successes = 64 conns × 8 tokens = 512 in both); `/bulk` count-IDENTICAL to the single-owner control (19,488/20,000 both) |
| blocking, owners=4 | 32 thr × 100 conns (22,400 reqs, 6.7 GB) | every stream byte-identical, 0 failures |
| uring, owners=8 | 48 thr × 100 conns (33,600 reqs, 10.1 GB) | every stream byte-identical, 0 failures |
| uring, owners=8 | identity hammer (28,000 reqs, 8.4 GB) CONCURRENT with ab -c 48 -n 60,000 `/bulk` | every stream byte-identical AND 60,000/60,000 ab complete, 0 failed |

Concurrency was REAL, not funneled: per-thread CPU during the owners=4 uring run
was 31/32/31/31 s across the four owners in a 32.4 s wall window (≈3.8 owners
continuously busy); owners=8 showed all seven attached owners at ≈38 s each in a
39.3 s window (≈7.7-way). Post-load sequential re-verification stayed
byte-identical; the process stayed alive through every phase; the server log
held exactly its two startup lines (no panic/fault). Totals across phases:
~15,360 verified streams ≈ 107,000 byte-checked requests ≈ 31 GB served
multi-owner, zero divergent bytes, zero transport failures, zero crashes.

## 3. Honest bounds — what this does NOT establish

- **Audit-grade, not proof-grade.** The no-shared-single-threaded-object
  invariant is a whole-program property maintained by convention at every seam.
  Nothing machine-checks it: a future seam that passes a `lean_object*` across
  threads (or routes TLS/admin/reconfig to an attached owner) reintroduces the
  race silently and would likely still pass light testing. A real proof needs
  either (a) a modeled gateway (loom-style exhaustive interleaving over an
  abstracted RC protocol) or (b) the per-owner-runtime redesign — which the
  current runtime does not support (module init installs process-global
  constants exactly once), i.e. per-owner PROCESSES (`--workers` already
  provides exactly that, at zero proof cost).
- **The persistence premise is observed, not contractual.** "Every generated
  object global is marked persistent" was verified against THIS build's emitted
  code (538 files, zero exceptions), not guaranteed by a documented toolchain
  contract. Re-run the audit after any toolchain bump.
- **Stress evidence is finite.** ~10⁵ concurrent crossings over minutes. A
  non-atomic RC race with a narrow window could sit below that. TSan on a
  debug-runtime build would raise the assurance class; not run here.
- **`DRORB_HEALTH_NATIVE` demo builds are EXCLUDED.** `health_serve` carries
  single-thread heap/GC statics and `serve_owner_loop` would run it on every
  owner: `DRORB_SERVE_OWNERS>1` + `DRORB_HEALTH_NATIVE=1` is a data race by
  construction. Keep them mutually exclusive (default builds do not link the
  native responder).
- Byte-identity was verified on the deployed DEFAULT serve paths (metered
  conformant + plain HTTP) over HTTP/1.1 + the gates; not separately hammered:
  ws frames, h2c, QUIC/UDP, TLS (those stay on owner 0 by wiring anyway).

## 4. Verdict

**Byte-identity and crash-safety with the lever ENABLED are now my-hand
verified at k=4 and k=8 on both IO hosts, and the runtime-model analysis gives
the reason it holds** (registered threads are ordinary runtime threads; the only
shared objects are deep-frozen persistent globals; per-call objects are
thread-confined). Enabled-mode safety is upgraded from "unverified, genuinely
risky" to "verified empirically with an audited safety argument and named
residuals". It is NOT a formal proof; the bounds in §3 stand, and the
zero-shared-heap alternative (`--workers`, per-owner processes) remains the
assurance-preferred scale-out where its memory cost is acceptable.
