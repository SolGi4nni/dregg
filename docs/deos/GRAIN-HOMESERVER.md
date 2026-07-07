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

## The three parts

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

## THE BODY — DECIDED: real Conduit via `execve`-grant (ember, 2026-07-07)

Full interop wins: a complete, spec-correct homeserver (federation, E2EE, any Matrix client), which
earns its heavier confinement. The body is **already available: `~/src/conduit`** (a full Conduit
Rust checkout — its own workspace + `rust-toolchain.toml` + `flake.nix`). We build it and run its
binary as the jailed grain body.

Cost, made precise — real Conduit needs **three firmament doors**, of which the grant surface today
(`deos-hermes/src/egress.rs`) has NONE: it grants only `grant_read(path)` (read-only) and
`grant_provider(host,port)` (outbound). The three new doors:

1. **`execve`-grant of exactly the conduit image.** The maximally-confined PD denies `execve`
   (`process-exec*`/`execve` denied — the reason the confined-agent body must BE a Rust peer today).
   Grant `execve` of ONE absolute image path (the built conduit binary) and nothing else — a named
   door, not lifting the exec wall. (`sandbox::Confinement` gains an `exec_allow: Option<PathBuf>`;
   macOS SBPL `(allow process-exec (literal "<path>"))`, Linux a seccomp `execve` arg-match on the
   image path.)
2. **A storage WRITE door.** `grant_read` opens a read-only subpath; Conduit's DB (rocksdb/sqlite)
   needs read+write to one dir. Add `grant_read_write(path)` — the write dual, one canonicalized
   subpath, sibling-denied, revocable (macOS `(allow file-write* (subpath …))`, Linux Landlock
   `LANDLOCK_ACCESS_FS_WRITE_FILE|MAKE_REG|…` on the dir).
3. **The inbound LISTEN door** (part (b) above) — bind+accept on exactly one `host:port`, the dual of
   the provider door. Preferred realization: the parent pre-binds the listener and passes the bound
   socket fd into the child's keep-list, so the child `accept()`s an fd it was handed and never holds
   raw `bind` authority (mirrors the Endpoint fd).

All three are firmament/kernel-adjacent. Per the be-thoughtful discipline they get a **design pass +
sound primitives**, NOT a swarm from thin context (this doc IS that pass). They are concrete
extensions of existing mechanisms (read→read_write, egress-out→listen-in, deny-exec→exec-one-image),
each a named door with deny-default and revocation — not a loosening of the jail's shape.

## The sequence (app layer in parallel; the three doors are the design-first kernel lane)

1. **Body de-risk (app, now):** build `~/src/conduit`; run its binary as a plain subprocess
   (unconfined), point two `deos-matrix` `MatrixClient`s at it, and drive the real card-carry loop
   (`card_carry` / `card_carry_bridge`) end-to-end — proving Conduit satisfies matrix-sdk over the
   membrane slice, and that this replaces the external Docker Conduit the Pillar-3 live test uses.
2. **The three firmament doors (kernel, design-first — THOUGHT before code):** `exec_allow`
   (one-image execve), `grant_read_write` (storage door), the listen door (pre-bound-fd). Each a
   named door, deny-default, revocable; each with a two-pole test (granted works / sibling denied).
   These land in `sel4/dregg-firmament/src/sandbox.rs` + `process_kernel.rs` + `deos-hermes` egress.
3. **The confined spawn (weld):** `spawn_pd_confined` a body that `execve`s the conduit binary with
   exactly {exec_allow=conduit, read_write=db-dir, listen=host:port, net_out=federation-peers if
   federating}. The card-carry clients dial the listen door.
4. **The lifecycle (reuse):** wrap it in `agent-platform` (rent/host/meter/reap) + `grain-turn` R2 so
   the homeserver-grain's lease is metered and its message-accepts are receipted turns.

Steps 1 and 2 are independent (app vs kernel) and can run in parallel; step 3 welds them. Step 2 is
NOT a thin-context swarm — it is the sound-primitive design lane, taken fresh.

## Payoff

Pillar 3's iron b-bar (two cockpits on two boxes co-driving a card) stops needing an external Conduit:
the localnet hosts its own membrane as a grain, cap-metered and R2-auditable. The last non-dregg-hosted
piece of the distributed inhabited world becomes dregg-hosted.
