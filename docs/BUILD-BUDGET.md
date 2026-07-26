# Build routing and budget — the current doctrine

This exists because a twelve-lane day drove the laptop to **load 400, 63 GB of swapfile, and zero
throughput**, and nobody could say what the safe number was; and because the *routing* half of the
answer went stale within nine days while lanes kept following it. Here is the arithmetic and the
routing.

**Scope.** Where to run a build, how to read its result, and how to clean up after it. If you are a
fresh lane and you read exactly one thing before starting a build, read the six lines below.

**Status.** Routing, box facts, and the VERDICT/ENVFAULT contract were re-measured **2026-07-26**;
the budget arithmetic further down was measured **2026-07-25** and still holds. Where a number came
from ember's own census rather than this file's re-measurement, it is attributed inline. See
[Superseded statements](#superseded-statements) for the older doctrine this replaces — several
places in the record still state it.

## Routing, in six lines

1. **Two remote boxes, both spare capacity for interactive work.** `persvati` and `hbox`. Balance
   across them; do not default everything to one.
2. **Cargo → a remote lane, never a second local build.** `scripts/pbuild <warm-lane> cargo test -p <crate>`.
   There is ONE lock per `target/` dir. Always `-p`; never `--workspace` to check one thing.
3. **Lean → wherever the Dregg2 oleans already are.** The laptop (2018 oleans) or `hbox`'s
   `eth-lc-air` lane (1948). Mathlib is *not* the scarce thing — the Dregg2 closure is.
4. **Read the `VERDICT` line, never the exit code.** `grep 'pbuild: VERDICT' <log>`.
5. **`REFUSED` and `ENVFAULT` are not results.** The build never ran, or the box killed it. No red
   and no green may be read off that log.
6. **Cleanup is `scripts/sweep-build-lanes.sh`, not `reclaim-space.sh`.** The latter requires a
   quiet swarm, which never happens.

## The three boxes

Measured 2026-07-26 00:01–00:20 ET unless attributed otherwise.

| | cores | RAM | free disk | warm cargo lanes | warm Lean | memory guard |
|---|---|---|---|---|---|---|
| laptop (Darwin arm64) | 12 | 96 GB | — | 1 shared `target/` per workspace | **2018 Dregg2 oleans** — the deepest anywhere | `scripts/swap-guard` (no cgroups on macOS) |
| `persvati` (Linux x86-64) | 24 | 83 GB (78 available) | 414 GB / 77% | **exactly 3**: `crewbraid`, `darkpool`, `native-anchor` | mathlib in 13 of 18 lanes, but ≤205 oleans | `earlyoom`, **prefers cargo/rustc/cc/ld**, avoids claude/node |
| `hbox` (Linux x86-64) | 24 | 123 GB | 107 GB / 76% | 2: `hcargo`, `eth-lc-air` | mathlib in 6 of 32 lanes; `eth-lc-air` has **1948 oleans** | `swarm-build` cgroup, `SWARM_MEM_MAX` default 96G; `earlyoom` **prefers poly/lean/leanc/cargo/rustc/Holmake** |

Both boxes were idle when measured: `persvati` load 0.77, `hbox` load 0.13 (its top process was
`ipfs` at 3.4% CPU).

**`hbox` is a spare box, deliberately.** It is the only self-hosted Actions runner and its listener
is still registered and running, but **nothing dispatches to it automatically any more.** Verified
2026-07-26 by parsing every workflow:

- `.github/workflows/lean-seed.yml:122` is the **only** self-hosted `runs-on` in the repo.
- That workflow's triggers are now **exactly `['workflow_dispatch']`** — manual only. The `push`
  trigger was removed in `29aa30ea3` and the nightly `schedule` after it.
- The other 7 distinct `runs-on` expressions all resolve to GitHub-hosted labels (61
  `ubuntu-latest`, 4 `ubuntu-22.04`, 1 `macos-14`, plus matrix variables that expand to
  ubuntu/macos only). `armed-teeth.yml:238` offers an `inputs.runner` override that **defaults to
  `ubuntu-latest`**. `release.yml`'s matrix is `dist`-generated and configures no custom runner.

So do not keep off `hbox`, and do not plan around it being CI-booked — that is the state that was
just removed, not the state to work around. The one thing that will occupy it is a **manual seed
cut** (below). `~/dev/datacake` (codex's HOL build) still exists there, last touched 2026-07-24,
with no `poly`/`Holmake` process running at measurement time — dormant, but it is a co-tenant that
can resume.

### Why Lean routing is about oleans, not mathlib

`pbuild`'s header (`scripts/pbuild:12`) says to keep Lean local because "persvati's Lean `.lake` is
cold/divergent". Re-measured, that is half right and the wrong half is the load-bearing one:

- **Not divergent.** Every warm lane on both boxes pins mathlib `inputRev`
  `1c2b90b13009c65b090d95a83c98e248deafb6f1` — byte-identical to `metatheory/lake-manifest.json`.
  `elan` resolves **Lean 4.30.0** inside a lane on both boxes (the repo's `lean-toolchain`), even
  though `hbox`'s *default* toolchain prints 4.17.0. A default-toolchain reading is not what a
  build gets.
- **But shallow.** Of `persvati`'s 13 mathlib-warm lanes, only 3 hold *any* Dregg2 oleans, and
  those hold **205** against the laptop's **2018**. So a `persvati` Lean build re-elaborates
  roughly 1800 modules. That — not a mathlib download — is the cost the old rule was reaching for.

**The rule that follows:** send Lean to the laptop, or to `hbox`'s `eth-lc-air` (1948 oleans) via
`scripts/hbuild`. `persvati` *can* build Lean and it will be correct; it will just be slow the
first time through. Concurrent `lake` builds in a shared `metatheory/` are fine — lake's own file
locks handle them — but bound the fan-out with `LEAN_NUM_THREADS`, because lake has no `-j`.

## Reading a result: the VERDICT line

`pbuild` prints exactly one authoritative line, on stdout, from an `EXIT` trap
(`scripts/pbuild:146`):

```
pbuild: VERDICT outcome=PASS|FAIL|REFUSED|ENVFAULT status=<n> lane=<lane> host=<host> cmd=<cmd>
```

```sh
grep 'pbuild: VERDICT' <log>     # the only line worth trusting
```

| outcome | meaning | what to do |
|---|---|---|
| `PASS` | the build ran and passed | read it as a green |
| `FAIL` | the build ran and failed | it is yours; fix it |
| `REFUSED` | **the build NEVER RAN** — a guard (cold lane, missing wrapper, disk floor, platform mismatch) stopped it | neither red nor green may be read from this log. Fix the refusal, rerun |
| `ENVFAULT` | the build STARTED and **the box killed it for memory** | ENVIRONMENT, not your code. Raise the cap or move boxes. **Retrying the identical command is wrong** |

**Never read the exit code**, and never `pbuild … ; echo "EXIT=$?"`. In a compound command `$?` is
the status of the trailing `echo`/`tail`, and a background-task notification saying "completed
(exit code 0)" reports on the last command of the compound. `pbuild:80-88` records three lanes in
one night reading a green that way — one of those "successes" had a log whose entire content was
the cold-lane refusal.

`REFUSED` vs `FAIL` is decided by *phase*, not by status number (`pbuild:129`), because a remote
`cargo` is free to exit 3 or 4 and a guard refusal must never be confusable with a real failure.

### ENVFAULT: the cap, never the box

ember's census (2026-07-25), recorded in `pbuild:104-127`: across 3111 `swarm-build` scopes on
`hbox` that reported a peak, **every one of the 67 killed scopes peaked at exactly a cap value**
(24G ×60, 32G ×5, 40G, 70G) and **not one of the 3044 survivors exceeded ~14G**. So an OOM-kill on
`hbox` is always the per-build `SWARM_MEM_MAX` cap — never slice pressure, never the box running
dry. Sixty of the sixty 24G kills trace to one copy-pasteable recipe
(`SWARM_MEM_MAX=24G swarm-build lake build …`) applied to Crypto/PQ modules that genuinely need
more. `swarm-build`'s own default is 96G; the 24G came from the recipe, not the tool.

**That recipe has since been raised, and the repo is clean of it.** Verified 2026-07-26 by grepping
every `.md` in the tree for `SWARM_MEM_MAX`: the only two hits are
`metatheory/Dregg2/Crypto/AXIOM-PICTURE.md:15` and `:20`, both now reading `SWARM_MEM_MAX=64G`. **No
copy-pasteable 24G cap survives in any document.** If you are running one, you inherited it from a
transcript or your own scrollback, not from the tree — raise it.

When you do hit `ENVFAULT`, in order: **raise the cap** (`SWARM_MEM_MAX=64G scripts/hbuild <lane>
<cmd>`), **narrow the unit** to one module so the peak is one module's peak, **bound the fan-out**
(`LEAN_NUM_THREADS=4`), then **serialize** — another lane may be sharing the cgroup ceiling. Both
`SWARM_MEM_MAX` and `LEAN_NUM_THREADS` are on `pbuild`'s forwarding allowlist
(`scripts/pbuild:484`); before they were, setting one and seeing no effect was its own expensive
confusion, because `ssh` does not carry the caller's environment.

Independently confirmed 2026-07-26: `swarm.slice` `MemoryMax` is 103079215104 bytes (96 GiB) and
its `memory.events` reads `oom 149 / oom_kill 86`.

The cost was never the kills — it was that nothing *told* the lane. `swarm-build` surfaces an
OOM-kill as an ordinary nonzero status, so from inside a lane it is indistinguishable from a proof
error. That is what `ENVFAULT` exists to name. On `persvati` the equivalent hazard has a different
shape: `earlyoom` there runs `--prefer '(cargo|rustc|rust-analyzer|cc|cc1plus|c++|ld|collect2|lld)'`,
so **a Rust build is the preferred victim** under memory pressure. On `hbox` the prefer-list also
includes `lean`/`leanc`/`poly`/`Holmake`.

### A bare SIGABRT with no Rust panic

That is **the Lean archive is absent** — the environment, not your code. `dregg-lean-ffi` links
`libdregg_lean.a` (~100–195 MB, gitignored, per-host); without it a build silently degrades to the
un-verified Rust executor ("marshal-only") and every `if !<x>_available() { SKIP }` gate reports
`ok` having asserted nothing. Do not "fix" it in your code, and **never** set `DREGG_REQUIRE_LEAN=0`
or `DREGG_ALLOW_UNAUDITED_PQ=1` to get past it — if you think you need one, that is a finding to
report. See `docs/LEAN-SEED-ARTIFACT.md` and `docs/BUILD-LEAN-LINKED-NODE.md`.

**Why lanes hit this, stated plainly.** The seed asset is content-keyed on
`platform + toolchain + mathlib rev + git rev-parse HEAD:metatheory/Dregg2`
(`scripts/lean-seed-key.sh:58`), and that `rev-parse` is written `|| true`. A remote lane dir has
**no `.git`** — verified 2026-07-26, `~/dregg-build/srot/.git` does not exist — so the tree
component comes back empty and the computed key can never match a published asset. Two consequences
stack:

- `scripts/fetch-lean-seed.sh` cannot work from inside a lane at all.
- With `lean-seed.yml` now manual-only, no HEAD-matching seed is cut automatically either, so even
  a correctly-keyed fetch will more often find nothing for the current tree.

Both roads end at marshal-only, which is the **false-red class**: a bare SIGABRT the lane reads as
its own bug. **Mitigation: cut a seed by hand before a session that needs verified-core tests on a
remote box.**

```sh
gh workflow run lean-seed.yml -f platforms=linux-x86_64
```

It is idempotent on the content key — ~23 s when nothing moved, ~20 min when the Lean tree did. Any
committed change under `metatheory/Dregg2/` invalidates every published asset for the new HEAD.

> **IN FLIGHT (lane `archive`, 2026-07-26):** `scripts/pbuild` is being changed to handle a missing
> archive rather than let it surface as a false red. Outcome not yet known; do not plan against a
> particular one. Re-read `scripts/pbuild`'s header before relying on this section's mechanics.

## Cleanup

**Use `scripts/sweep-build-lanes.sh`.** It sweeps **per idle lane** and deletes only **superseded
artifact generations**, so it needs no global quiet moment:

```sh
scripts/sweep-build-lanes.sh                        # report every lane, delete nothing
scripts/sweep-build-lanes.sh --apply                # sweep every IDLE lane
scripts/sweep-build-lanes.sh --lane crewbraid --apply
scripts/sweep-build-lanes.sh --host hbox --apply
```

Cargo names artifacts `<crate>-<16 hex>` where the hash keys package+features+profile+deps. When
`Cargo.lock` or a feature set moves, the old hash is orphaned forever — never reused, never
collected. Deleting an orphan generation cannot produce a wrong build: a fingerprint miss is a
rebuild, never a silent stale link. ember's measurement (2026-07-25) put the orphan share at
roughly **three quarters of a mature lane** (`darkpool` 171.7 GB orphan vs 57.0 GB keep;
`crewbraid` 166.8 GB vs 114.2 GB), and one pass reclaimed **332.5 GB**. Independent cross-check
2026-07-26: `persvati:~/dregg-build` now measures **450 GB across 18 lanes**, against the **611 GB**
recorded on 07-25 — the sweep landed, and the three cargo lanes have since rebuilt into part of it
(`darkpool` 194G, `crewbraid` 130G, `native-anchor` 106G = 96% of the total).

**`scripts/reclaim-space.sh` is superseded for this purpose.** It deletes whole `target/` dirs, so
its own header (`scripts/reclaim-space.sh:22`) warns it "RACES ACTIVE BUILDS: Run it when the
swarms are quiet" — and with ~10 concurrent terminals that precondition is unsatisfiable. It is
still the right tool for the *narrow* job of surveying build sprawl across `~/dev` when you
genuinely have a quiet machine; it is **not** the routine lane sweep, and any pointer calling it
"the sprawl sweep" sends a reader at a tool that will correctly refuse them.

⚠ **Known gap, in `sweep-build-lanes.sh`'s own header: process-absence is not lane-ownership.** Its
liveness probe looks for `cargo`/`rustc`/`lake`/`lean` attributed to the lane, but an agent that
*owns* a lane spends most of its wall-clock not compiling. In that window the lane reads idle and
gets swept. ember did exactly this to two live agents on 07-25. The `.pbuild-lease` file exists to
close that gap: one line, `owner=… pid=… host=… expires=<unix-seconds>`, written by `pbuild` and
honoured by the sweeper, a **hint with an expiry** rather than a lock so a stale lease cannot wedge
a lane forever. It must never be committed — `.gitignore:106` covers it, and that entry is
load-bearing beyond hygiene, because `pbuild` syncs with `rsync --delete --filter=':- .gitignore'`
and without the ignore an rsync would strip a live lease.

> **IN FLIGHT (lanes `lease` and `archive`, 2026-07-26):** the lease writer/reader pair and a new
> `scripts/lane-lease.sh`. The format above is the agreed contract; the implementations are landing.

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
- **hbox: bound by `swarm-build`'s cgroup**, which also applies `taskset -c 0-15 nice -n 15` — so a
  build there is confined to 16 of 24 cores and yields to interactive work by design.
- **Lean (`lake`) has no `-j`/`--jobs`** in this toolchain — `build.rs` probes for it, and passing
  a flag the binary rejects turns `lake build` into an *immediate hard failure* rather than a
  bounded one. The `-j <n>` that stood in the build script for ~95 minutes on 2026-07-25 bounded
  nothing and sent every non-strict build down the restore-the-seed path
  (`dregg-lean-ffi/build.rs:707-713`). **Two knobs exist and they are not interchangeable — pick by
  how you are invoking Lean:**

  | invocation | the knob that binds | why |
  |---|---|---|
  | `lake build <Module>` **run directly** (what the routing section above tells you to do) | **`LEAN_NUM_THREADS=<n>`** | it is the `lean` task-pool size, "the cap that actually applies today" (`dregg-lean-ffi/build.rs:212-213`). Measured: unset → 10–12 concurrent `lean` on 12 cores, `=4` → exactly 4, `=2` → exactly 2 |
  | a **cargo** build that runs `dregg-lean-ffi/build.rs` | **`DREGG_LEANC_JOBS=<n>`** | it overrides `configured_leanc_workers()` (default half the cores, ≤ 8), which the script uses for the `leanc` phases *and* feeds into `LEAN_NUM_THREADS` for its own `lake build` (`build.rs:295`, `:715-718`). An outer `LEAN_NUM_THREADS` is an operator decision and is honoured as-is |

  ⚠ So `DREGG_LEANC_JOBS=2` does **nothing at all** for a bare `lake build` — it is only read by
  that build script. For a direct Lean build, and with more than one Lean lane live, set
  `LEAN_NUM_THREADS=2`. The cap is applied per *build script*, so N cargo lanes multiply it.
  `build.rs` now checks the budget against the children `lake` actually spawned rather than
  trusting it because it was passed (`build_parallel::run_bounded_lake`) — a containment measure
  that silently disarms the verified runtime is worse than none.

**Total across everything: ~4 concurrent build-heavy lanes.** Read-only lanes (survey, census,
design, doc) are free — fan those as wide as you like.

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
is possible.** A lane name existing on disk says nothing about warmth: remote lanes live at
`~/dregg-build/<lane>` (`scripts/pbuild:170`), and a cold one is refused on purpose because it
would re-run every build script including the mathlib-sized one.

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
  ember measured that lock held **45+ minutes with 163 cargos queued**, which blinded an auditor
  for a whole window; a queued cargo looks exactly like a slow build from inside a lane.

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
5. Did I read the `VERDICT` line rather than the exit code?

## Superseded statements

These appear in the record and are wrong as routing guidance now. The record is append-only, so
they are corrected here rather than rewritten there.

| stated | where | correction |
|---|---|---|
| "heavy Rust → persvati; Lean → local lake; **G1/RAM-bound → hbox**" | `HORIZONLOG.md:657` (2026-07-17) | The three-way split assumed hbox was reserved for RAM-bound outliers. Both boxes are now general spare capacity; pick by what is *warm* and what is *idle*, not by workload class. |
| "**persvati is MARSHAL-ONLY** (no Lean sysroot) … provisioning `DREGG_LEAN_SYSROOT` would remove the split" | `HORIZONLOG.md:664` (2026-07-16) | Stale. `persvati` has Lean **4.30.0** and `elan` resolves the repo toolchain inside a lane. The residual constraint is not a missing sysroot, it is **olean depth** (≤205 vs 2018 local) and a per-lane `libdregg_lean.a`. "Marshal-only" remains correct and current as a *build-mode* term everywhere else it appears in `docs/`. |
| "`scripts/reclaim-space.sh` is the sprawl sweep" | `HORIZONLOG.md:663` (2026-07-16) | Superseded by `scripts/sweep-build-lanes.sh` for lane cleanup; `reclaim-space.sh --clean` cannot legitimately run during a swarm. |
| "hbox is idle" / "hbox is triple-booked, keep off it" | field lore, both directions, 2026-07-25 | Both were sampling artifacts of the same cause. `lean-seed.yml`'s `push` trigger made hbox busy 19–25 min at a time on the most-edited path in the tree; between runs it looked idle. That trigger and the nightly are **gone** — hbox now carries zero automatic CI load and is spare on purpose. The rationale comment at `.github/workflows/lean-seed.yml:37` still reads "triple-booked"; that is the dated reason the trigger was cut, not current routing. |
| "check the exit code" (any doc, about any build wrapper) | — | Read the **`VERDICT`** line. No such phrasing survives in `docs/`; if you add one, this is the correction. |
| "`--workspace` to check one thing" | — | Always `-p <crate>`, narrowed. One lock, measured held 45+ min. |

### Not superseded, and worth restating

`AGENTS.md`'s "Do NOT run a full `--workspace` debug build locally", the cold-lane refusal, and
"Lean is not something to casually offload" are all still right. What changed is the *reason*
(oleans, not mathlib) and the *set of boxes available* (two, both spare).

## Open / unverified

- **Debug-info bloat — the low end is now re-derived, not just reported.** ember measured **83–92%
  of every debug binary is DWARF** that nothing in this repo reads (`.text` was 107 MB of a 1.46 GB
  binary). Independently reproduced 2026-07-26 on `persvati:~/dregg-build/darkpool`, the six largest
  debug binaries, via `size -A`:

  ```
  dreggnet_web_server-683807d3dd9d6835   total=1497MB  .text=107MB  .debug_*=1249MB  83%
  demo_playthrough-2f5e699dd3a633cb      total=1482MB  .text=106MB  .debug_*=1236MB  83%
  server-2bf01b18f63e242c                total=1482MB  .text=106MB  .debug_*=1236MB  83%
  metrics_surface-c7c6cfb8f0ea7396       total=1481MB  .text=106MB  .debug_*=1236MB  83%
  descent_funnel-fcc7261f2ca8beb6        total=1481MB  .text=106MB  .debug_*=1236MB  83%
  persistence-edcda51b9ae3dff5           total=1481MB  .text=105MB  .debug_*=1236MB  83%
  ```

  All six at 83%; the 92% upper end is ember's and is not re-derived. ⚠ **This check only works on
  Linux.** On the Darwin laptop `size -m` on the same kind of binary reports ~0 for `__DWARF`,
  because macOS leaves debug info in the `.o` files plus a debug map rather than in the linked
  binary — a laptop reading is not a refutation. **IN FLIGHT (lane `profile`)**: the workspace-root
  profile is being changed (an uncommitted +43-line change to `Cargo.toml`'s profile section at the
  time of writing). No claim is made here about the resulting state — read `Cargo.toml`.
- **`box-health.sh`** (to land under `scripts/`) — a one-shot "which box is warm and idle right
  now" probe. **IN FLIGHT (lane `hygiene`)**; it did not exist when this was written, which is why
  it is named here without a path — a path reference would be a dead one. Until it lands, the
  measurements in [The three boxes](#the-three-boxes) are point-in-time and you should re-check
  load yourself before a heavy build.
- **The 12.4 GB of unreclaimable tmpfs** ember freed from inside the `swarm.slice` cap on 07-25
  (shmem 13.5G → 1.1G) is ember's measurement, not re-derived here.
