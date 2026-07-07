# The Matrix homeserver as a grain — dregg hosts its own membrane

*Design note (2026-07-07). Turns Pillar 3's external-Conduit dependency into a dregg-native confined
body: the homeserver the co-driven-card membrane rides is a hosted, cap-metered, R2-verifiable grain
— "dregg is the host" all the way down. Companion: `GOAL-DISTRIBUTED-DEOS.md` (Pillar 3),
`THE-GRAIN.md`, `LOG-A-HERMES-IN.md` (the confinement machinery).*

## Why

Pillar 3 (co-driven cards) carries a `CardForkEnvelope` in a Matrix `MembraneEnvelope` over a live
homeserver — today an **external Conduit** (`deos-matrix` is a `matrix-rust-sdk` *client*; there is
no homeserver in-tree). That external trusted server is the one piece of the distributed inhabited
world that is NOT dregg-hosted. Hosting the homeserver as a grain closes that: the membrane's relay
becomes a confined body with a granted door, a metered lease, and effects that are verifiable turns —
and it keeps Matrix-ecosystem interop (any Matrix client can still join a room).

## ⚑ ARCHITECTURE REVISION (2026-07-07, supersedes the three-door plan below): LIB-EMBED, ONE DOOR

Two census facts collapsed the confinement cost:
- **The conduit lineage is `[lib]` + a thin `[[bin]]`** — so the homeserver is COMPILED INTO the
  grain body as a Rust library (exactly as the confined brain is compiled into the PD body). The
  `execve` door DISSOLVES: no exec grant, tightest jail, and the body can weld dregg machinery
  (receipted message-accepts, metering) directly instead of wrapping a black-box process.
- **`Confinement::with_fds` already exists** (`sandbox.rs:109`) — the parent pre-binds the
  `TcpListener` and hands the bound fd into the child's keep-list; the child `accept()`s an fd it
  was GIVEN and never holds bind authority (the Endpoint-fd pattern). The listen door DISSOLVES
  into existing machinery.
- Remaining NEW door: **`grant_read_write(path)`** for the homeserver's DB dir (RocksDB) — the
  write dual of `grant_read`, one canonicalized subpath, sibling-denied, revocable. ONE door.
  (Endgame curiosity, not this slice: sandstorm-bridge already models grain `/var` = a cell's umem
  heap; a sqlite-backed server could eventually checkpoint AS a cell. RocksDB won't ride umem.)

**THE BODY — REVISED PICK (live-scouted 2026-07-07): `continuwuity`**
(canonical https://forgejo.ellis.link/continuwuation/continuwuity, mirror codeberg.org/continuwuity).
The conduwuit lineage's community continuation: commit-fresh (last commit the day before the scout),
multi-maintainer (real bus factor), release every week or two, matrix.org-listed **Stable**, spec
v1.8–1.14 with a rewritten sync proven against matrix-r

**(a) The body — a homeserver serving the CS-API subset the membrane needs.** `deos-matrix`'s
`matrix-rust-sdk` client exercises a bounded slice of the client-server API: the `/_matrix/client/
versions` handshake, password login, `/sync`, and room message send/receive (the `MEMBRANE_EVENT_KEY`
`m.room.message`s). The body must satisfy exactly what matrix-sdk expects over that slice. Two shapes
(the open fork — see below).

**(b) The new capability — an inbound "listen door" (kernel-adjacent; design-first).** Firmament
confinement today grants `net_out: Vec<String>` — an *outbound* provider-egress allow-list
(`spawn_pd_confined_with_surface_and_egress`, `process_kernel.rs:1345`). A homeserver is *listened
to*: it must bind a port and accept inbound connections. That is a **new** grant shape, the dual of
the provider door:
- **Linux:** pre-bind the listener in the parent and pass the bound socket fd into the child's
  keep-list (the child never needs raw bind authority — it `accept()`s on an fd the host handed it,
  exactly as the Endpoint fd is handed today), OR a seccomp `bind`/`accept`-notify door that admits
  exactly one `host:port`. The child's netns stays otherwise empty — deny-default holds.
- **macOS Seatbelt:** an SBPL `(allow network-inbound (local tcp "*:PORT"))` rule scoped to the one
  port, mirroring the outbound `(allow network-outbound (remote ip …))` provider rule.
This is a firmament/kernel change. Per the be-thoughtful discipline it gets a **design pass + a
sound listen-door primitive**, not a swarm from thin context. It is the ONE genuinely new mechanism.

**(c) The lifecycle — a metered, R2 grain (reuses what exists).** `agent-platform`
(rent/host/meter/reap confined grains) + `grain-turn` (R2: a body's effects are committed executor
turns) already model a hosted confined body. The homeserver grain plugs in: its lease is
cap-metered, its lifecycle reaped, and — the interesting part — room membership / message-accept can
be surfaced as verifiable turns (a room is a cell, a message an event; the homeserver-grain's accept
of a message is a receipted turn, so the relay itself is auditable, not a trusted black box).

## THE BODY — DECIDED: continuwuity, embedded as a LIBRARY (ember + live scout, 2026-07-07)

Full interop wins (federation, E2EE, any Matrix client), and the census + a live homeserver scout
turned the "which server / how confined" question into a much tighter answer than the first draft's
`~/src/conduit`-via-execve:

**The pick: `continuwuity`** (`https://codeberg.org/continuwuity/continuwuity`, canonical
`https://forgejo.ellis.link/continuwuation/continuwuity`). Why over the alternatives (scout, live
July 2026): conduwuit is **Obsolete** (discontinued ~Apr 2025); continuwuity is the community
continuation — committed *yesterday*, ~7.3k commits, weekly-ish releases, matrix.org-listed **Stable**,
**multi-maintainer** (real bus factor), a rewritten sync proven against Element X / matrix-rust-sdk,
Apache-2.0, and a **proper rlib workspace** (`conduwuit-{core,api,service,database,router,admin,…}`,
the main crate declaring `[lib] crate-type=["rlib"]`). Runner-up `tuwunel` (matrix-construct/Volk,
Swiss-government-sponsored — the "Matrix Foundation adjacency" rumor is UNCONFIRMED/false) has the
single cleanest embed shim (`Runtime::new → Server::new → exec`) but single-lead bus factor +
enterprise orientation. `grapevine` skipped (no releases ever, dormant, pre-conduwuit feature level).
Non-lineage: `palpo` (new, good — but PostgreSQL, kills self-contained embedding). ⚠ continuwuity's
critical deps are git-pinned forks (ruma + rust-rocksdb) on their own forgejo — **pin exact revs,
consider vendoring**; crates still named `conduwuit-*`, main is calendar-alpha → expect internal API
churn between releases.

**The architecture SIMPLIFIED — the "three doors" collapse to ONE.** The first draft assumed we
`execve` a homeserver binary. But the conduit lineage is `[lib]` + a thin `[[bin]]` wrapper, so we
**embed the homeserver as a Rust library compiled INTO the grain body** — exactly like the confined
brain is a Rust ACP peer compiled into the PD, not an `execve`'d process. Consequences:

1. **The execve door DISSOLVES.** No `execve` grant — the homeserver runs *as the body*, so the jail
   keeps its tightest shape (`process-exec*`/`execve` stays denied). The body can also weld dregg
   things directly (receipted message-accepts, metering) instead of wrapping a black-box process.
2. **The listen door MOSTLY dissolves.** `Confinement::with_fds` (`sandbox.rs:109`) already hands a
   child a keep-list of fds. The parent **pre-binds the `TcpListener`** and passes the bound socket
   fd in; the child `accept()`s on an fd it was handed and never holds raw `bind` authority (the
   Endpoint-fd pattern, already proven). No new bind/accept syscall door needed for the common case.
3. **The ONE remaining door: `grant_read_write(path)`** — the storage write dual of `grant_read`.
   continuwuity is **RocksDB-only** (a C++ build dep, file-system-hungry), so the body needs read+write
   to exactly one DB dir: one canonicalized subpath, sibling-denied, revocable (macOS `(allow
   file-write* (subpath …))`, Linux Landlock `LANDLOCK_ACCESS_FS_WRITE_FILE|MAKE_REG|MAKE_DIR|…`).
   This is the only genuinely new firmament grant — a concrete extension of the existing read door.

That single door is still firmament-adjacent → design-first, sound primitive + two-pole test (granted
dir writable, sibling denied), NOT a thin-context swarm (this doc is the design pass). But it is one
door, not three — the lib-embed decision paid for itself.

**Non-Rust homeservers ride the sandstorm rail.** Synapse (Python) / Dendrite (Go) can't embed as a
lib, but `sandstorm-bridge` already models a grain as an `.spk`-packaged execve-in-chroot body with
`/var` = a cell umem heap. So a heavy homeserver ships as a sandstorm grain (its own confinement
story) while the Rust pick gets the tight native lib-grain — both worlds covered by the two rails.

## Recon (2026-07-07, continuwuity cloned + inspected — `~/src/continuwuity-recon`, HEAD `4454e540`)

Grounded, embed-ready:
- **Workspace `src/*`:** `core · api · service · database · router · admin · web · macros · main ·
  build_metadata · ruminuwuity`. The `main` crate (pkg `conduwuit` 26.6.0-alpha.1, edition **2024**)
  has `[lib] path="mod.rs" crate-type=["rlib"]` **and** a `[[bin]]` — so we depend on the LIB.
- **The boot seam (`src/main/mod.rs`):** `pub fn run_with_args(args: &Args)` — builds a tokio
  `runtime::new(args)`, `Server::new(args, Some(handle))?` (`Arc<Server>`), spawns `signal::signal`,
  `block_on(async_main)` → `router::run(...)` (the axum HTTP server that binds the listener), then
  `runtime::shutdown`. An embedder calls `run_with_args` on a thread; the `Arc<Server>` is the
  graceful-shutdown handle. `Args { config: Option<Vec<PathBuf>>, option: Vec<String> (TOML k=v
  overrides), maintenance, console, .. }` (`src/main/clap.rs`).
- **Deps:** `ruma` is pinned to **mainline** `github.com/ruma/ruma` (NOT a fork — good); the real
  forks are `rust-rocksdb` (`forgejo.ellis.link/continuwuation/rust-rocksdb-zaidoon1`) + jemalloc /
  rustyline-async / event-listener on their forgejo. RocksDB (C++) is the build tax.
- **Minimal boot config** (`conduwuit-example.toml`): `server_name`, `address=["127.0.0.1"]`, a test
  `port`, `database_path` (a temp dir), `allow_registration=true`, `allow_federation=false`,
  `listening=true`.

**Vendoring decision: an ISOLATED excluded workspace** (like `discord-bot`/`dregg-tui`) — a new
`deos-homeserver` crate that git-deps `conduwuit` at a pinned rev with its own `rust-toolchain.toml`
(continuwuity is edition-2024 / toolchain-pinned; isolating it keeps its heavy pinned-fork dep graph
OUT of the breadstuffs root resolution). True source-vendoring (copy-in for offline/reproducibility)
is a later step once the embed is proven. **GATE: a `cargo check -p conduwuit` in the recon clone is
running to confirm it builds in this env (edition 2024 + the rocksdb fork's C++) BEFORE any wiring.**

## The sequence (app layer now; ONE firmament door, design-first)

1. **Body de-risk + embed seam (app, now):** vendor/pin continuwuity (exact revs of it + its ruma /
   rust-rocksdb forks), stand its homeserver up **in-process as a library** (the rlib workspace entry
   — for tuwunel the documented `Runtime::new → Server::new → exec` shim; for continuwuity the
   equivalent `conduwuit-router`/`service` boot), point two `deos-matrix` `MatrixClient`s at it over a
   plain loopback listener, and drive the real card-carry loop (`card_carry` / `card_carry_bridge`)
   end-to-end — proving the embedded server satisfies matrix-sdk over the membrane slice and replaces
   the external Docker Conduit the Pillar-3 live test uses. No jail yet. (RocksDB is the real tax: a
   C++ build dep + a hungry db dir — note the dir for the one door.)
2. **The ONE firmament door (kernel, design-first — THOUGHT before code):** `grant_read_write(path)`,
   the storage write dual of `grant_read` — one canonicalized subpath (the RocksDB dir),
   sibling-denied, revocable; a two-pole test (granted dir writable / sibling denied). Lands in
   `sel4/dregg-firmament/src/sandbox.rs` + `process_kernel.rs` + `deos-hermes/src/egress.rs`. (The
   execve door is gone — lib-embed; the listen door is the existing `with_fds` pre-bound-fd pattern.)
3. **The confined spawn (weld):** `spawn_pd_confined_with_surface_and_egress` a body that RUNS the
   embedded homeserver with exactly {read_write=db-dir, listen=the pre-bound fd, net_out=federation
   peers if federating}. `execve` stays denied. The card-carry clients dial the listen door.
4. **The lifecycle (reuse):** wrap it in `agent-platform` (rent/host/meter/reap) + `grain-turn` R2 so
   the homeserver-grain's lease is metered and its message-accepts are receipted turns.

Steps 1 and 2 are independent (app vs kernel) and can run in parallel; step 3 welds them. Step 2 is
NOT a thin-context swarm — it is the sound-primitive design lane, taken fresh.

## Payoff

Pillar 3's iron b-bar (two cockpits on two boxes co-driving a card) stops needing an external Conduit:
the localnet hosts its own membrane as a grain, cap-metered and R2-auditable. The last non-dregg-hosted
piece of the distributed inhabited world becomes dregg-hosted.
