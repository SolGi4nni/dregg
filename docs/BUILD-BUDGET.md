# The build budget — measured, 2026-07-25

This exists because a twelve-lane day drove the laptop to **load 400, 63 GB of swapfile, and
zero throughput**, and nobody could say what the safe number was. Here is the arithmetic.

## The two boxes

| | cores | RAM | warm build lanes |
|---|---|---|---|
| laptop (Darwin arm64) | 12 | 96 GB | 1 shared `target/` per workspace |
| persvati (Linux x86-64) | 24 | 78 GB free | **exactly 3** — `native-anchor`, `crewbraid`, `darkpool` |

**Only three persvati lanes are warm.** Every other `dregg-build/*` dir reads 0 deps and
`pbuild` refuses it — correctly, because a cold lane re-runs every build script including the
mathlib-sized one. A lane name existing on disk says nothing about warmth.

⚠ **"Warm" is TWO independent axes and only one is checked.** `pbuild`'s guard counts
`target/debug/deps`; `dregg-lean-ffi/libdregg_lean.a` is separate, per-lane and arch-specific,
and **its absence is invisible to the guard**. Measured: `native-anchor` passed the warmth
check with *no archive at all*. Check both:

```sh
ls <lane>/target/*/deps | wc -l          # cargo warmth
nm -g <lane>/dregg-lean-ffi/…/libdregg_lean.a | grep -c ' T dregg_'   # executor warmth
```

A missing archive is fixable in **2m14s** by building one natively on that box (mathlib is
cached). For eight hours four lanes read `pbuild`'s correct refusal to cross-ship a Mach-O
archive as *"persvati cannot do this"*. **A refusal message tells you what happened, not what
is possible.**

## The unit cost

Measured across 50 concurrent jobs: **~0.98 GB per `rustc`/`leanc` process.** A Lean elaboration
of a Crypto/PQ module peaks far higher — 2.2 GB and 3.5 GB observed on single processes.

## The ceiling, and why 12 lanes was never going to work

**Cargo defaults `-j` to core count.** Two concurrent `cargo` invocations on a 12-core box is
24 jobs, not 12 — the default is per-invocation and does not know about its siblings. At twelve
lanes we measured **50 concurrent compile processes on 12 cores**: 4× oversubscription, 49 GB of
demand, and *less* work completed than one lane would have done alone.

> **Oversubscription past core count buys nothing and costs a gigabyte per job.**

So the budget is:

- **Laptop: ONE build-heavy lane at a time.** Two is already 24 jobs. If a second must run,
  `CARGO_BUILD_JOBS=6` on both.
- **persvati: THREE build-heavy lanes**, one per warm dir, `-j8` each = 24 jobs on 24 cores.
- **Lean (`lake`) is LOCAL and bounded by `DREGG_LEANC_JOBS`** — this toolchain's Lake has **no
  `-j`/`--jobs`** and `build.rs` probes for it; reintroducing that flag broke every Lean build
  for a day. The cap is applied per *build script*, so N lanes multiply it. With more than one
  Lean lane live, set `DREGG_LEANC_JOBS=2`.

**Total across everything: ~4 concurrent build-heavy lanes.** Read-only lanes (survey, census,
design, doc) are free — fan those as wide as you like.

## Swap is not a buffer, it is damage

`scripts/swap-guard` kills build processes when swap crosses 2 GB. macOS has no cgroups, so
there is no per-process `MemoryMax` the way `swarm-build` gives on hbox; the gauge plus a
targeted kill is the available instrument.

Two reasons swap is worse than an OOM here:

1. **The SSD.** macOS grows swapfiles on demand and they are real writes — 62 GB in one day.
2. **Throughput goes to zero SILENTLY.** A thrashing build is indistinguishable from a slow one
   from inside a lane: the log keeps its last line, the process stays alive, nothing reports
   *"you are now paging"*. One lane measured its own `rustc` at **~7% of a core**. Another
   burned 34 minutes on a run that never started.

A killed compile costs minutes and is crash-safe (cargo and lake both resume). A thrashing box
costs hours and takes every co-tenant lane with it.

## Three failure modes that look like a slow build

- **An ORPHANED test binary.** When a wrapper is reaped its `cargo` dies with it — but a test
  binary already spawned does not. It becomes `PPID 1` and runs forever. One
  (`dregg_circuit_prove … shielded`, from a private `CARGO_TARGET_DIR`) held **35 GB for 25
  minutes** reporting to nobody. Sweep: `ps -Ao pid,ppid,command | awk '$2==1 && /deps\//'`.
- **`ps` RSS undercounts a paged-out process by an order of magnitude** — it read 2.4 GB for
  that 35 GB process. Use `footprint -p <pid>` (`phys_footprint`), which is what Activity
  Monitor shows.
- **Two of your OWN `cargo` invocations deadlocking each other** on one `target/` lock —
  observed by a lane, on itself. Before starting a build, check whether you already have one.

## A private `CARGO_TARGET_DIR` is never the answer

It looks like lock isolation and it is a cold target dir: every build script re-runs, including
`dregg-lean-ffi`'s mathlib-sized path. `pbuild <warm-lane>` gives real isolation with a warm
cache. `git archive HEAD | ssh <host> "cd <lane> && tar -x"` gives a *known-good tree* remotely,
which plain `pbuild` does not — it rsyncs the working tree and therefore inherits every
sibling's uncommitted churn.

## Before you start a build, ask

1. Is one already running that answers my question? (Read its log — but see below.)
2. Am I the only build-heavy lane on this box right now?
3. Warm lane, and does it have an archive if I need the executor?
4. Fresh log path in a `mktemp -d`? (A reused path truncated under a live writer produces a
   NUL-gapped file, on which **`grep` silently matches nothing** — and empty reads as clean.)
