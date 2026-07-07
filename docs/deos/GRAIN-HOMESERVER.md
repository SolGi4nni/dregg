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

## THE OPEN FORK (needs ember)

- **Minimal purpose-built homeserver as the grain body.** A Rust homeserver serving only the CS-API
  subset above, compiled INTO the grain body (no `execve` — the maximally-confined PD denies it, so
  this keeps the jail tight). Fully confined, R2-able, small. Cost: it must satisfy matrix-sdk's real
  expectations over the slice (version negotiation, login/sync response shapes, room-event ordering)
  — a real but bounded implementation effort; it is NOT a general homeserver (no federation, no E2EE
  device management beyond what the card-carry needs).
- **Real Conduit (conduwuit) as the grain body via an `execve`-grant.** A complete, spec-correct
  homeserver (federation, E2EE, any client) — but running it means granting `execve` of exactly the
  conduit image (the "grant execve of exactly the agent image" seam), a bigger jail hole, plus a
  storage door for its DB. Heavier jail, full interop.

The on-thesis default is **minimal purpose-built** (tightest jail, no execve, fully R2) unless full
federation/interop is the point — in which case **real Conduit** earns its heavier confinement.

## The first buildable slice (no kernel change — app layer in parallel)

The body can be prototyped and proven BEFORE the listen door exists: run the minimal homeserver over
a plain in-process `TcpListener` on loopback (no jail), point two `deos-matrix` `MatrixClient`s at it,
and drive the real card-carry loop (`card_carry` / `card_carry_bridge`) end-to-end — proving the body
satisfies matrix-sdk over the membrane slice. THEN jail it once the listen-door primitive is designed
and sound. This is the "app layer in parallel while the kernel bit gets thought" pattern: the
homeserver-body lane and the firmament listen-door lane are independent until they weld.

## Payoff

Pillar 3's iron b-bar (two cockpits on two boxes co-driving a card) stops needing an external Conduit:
the localnet hosts its own membrane as a grain, cap-metered and R2-auditable. The last non-dregg-hosted
piece of the distributed inhabited world becomes dregg-hosted.
