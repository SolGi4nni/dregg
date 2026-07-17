# dregg as a DATA PLANE

dregg is usually described as a *control / auth plane*: capabilities, attenuation,
verified turns, conserved state, unforgeable receipts. This document is about the
other face. The same substrate is also a **data plane** — the bus apps actually
move work across. Queues, mailboxes, wake-by-name, event-notify, pub/sub, streams:
all of it, cap-gated and receipted, grounded in verified turns.

The userspace surface lives in `captp/src/data_plane.rs` (the `Bus`). It is a thin,
coherent buff over primitives that already exist in `captp/` — it does not invent a
new transport, it *exposes* the one dregg already has.

## What an app gets

A deos surface, Hermes, or the harness holds a `Bus` and calls:

| op | method | what it is |
|----|--------|------------|
| ENQUEUE work to a cell's inbox | `Bus::enqueue` | put a payload on a recipient's spool; get a signed `Delivery` receipt back |
| be WOKEN by name | `Bus::wait` / `Bus::poll_wake` | event-notify: the inbox cursor advanced |
| SUBSCRIBE to a topic | `Bus::subscribe` | join a pub/sub fan-out group |
| PUBLISH to a topic | `Bus::publish` | fan a payload to every subscriber's inbox, one receipted enqueue each |
| DRAIN the inbox | `Bus::drain` | take the queued boxes AND witness their delivery |

Each op is **cap-gated** (a `SendCap`) and **receipted** (a `Delivery` carrying a
`CustodyReceipt`). The cap is an `AuthRequired`-bearing edge: it can be attenuated
(`SendCap::attenuate`, non-amplifying) and revoked (`SendCap::revoke`), and an
enqueue that the cap does not admit is **refused at the seam** — before anything is
queued, so no receipt is minted and the ledger never shows phantom work.

## The comms primitive inventory

- **Queue / mailbox / spool** — `crate::store_forward::MessageRelay`, a
  per-recipient FIFO inbox. `Bus::enqueue` writes to it; `Bus::drain` empties it.
- **Wake / event-notify** — `data_plane::Waker`, a per-channel monotone cursor plus
  per-waiter last-seen marks. A wake is *derived* from the cursor, never asserted.
- **Pub/sub** — the `Bus` topic table: `subscribe` joins, `publish` fans out to
  every subscriber as a real enqueue (each with its own receipt + wake).
- **Stream** — a channel name polled repeatedly: `poll_wake` → `drain` → `acknowledge`
  is a stream cursor loop. Causal order within a recipient's inbox is preserved by
  the relay's per-sender `causal_sequence` (see `store_forward`).
- **Receipt** — `data_plane::Delivery` (the promise) + the drain-witness log (the
  fact). `CustodyReceipt` signs the promise; `InboxState::from_dequeue` reads the fact.

The **append-only log of record** under all of this is the blocklace (`blocklace/`):
the store-and-forward envelope (`store_forward::BlocklaceEnvelope`) is exactly how a
queued box rides the DAG to an offline recipient. The data plane is the userspace
shape; the blocklace is the durable spine.

## Receipt-identity: queued is NOT handled

This is the load-bearing invariant — the one buildr's fleet would not give up. A
thing on the spool is not a thing handled. In the `Bus` the two states are
*separate objects*, never the same flag:

- **queued** lives in the relay (`pending_count`), and is *promised* by the
  `Delivery::receipt` — a signed statement "this box is in the inbox".
- **handled** lives in the drain-witness log (`delivered_hashes`), and is *witnessed*
  by `Delivery::is_handled` — which reads the content hashes a `drain` actually
  emitted, never the receipt.

So you can hold a perfectly valid receipt for a box that was never drained, and
`is_handled` returns `false`. Past the custody deadline, that box's relay is
*convictable* (`adjudicate_from_inbox` → slash). A box that *was* drained flips the
witness and the relay is *acquitted*. The promise and the witness can never be
confused, because they are read from different places. (Tests:
`enqueue_wake_drain_witness_lifecycle`, `undrained_is_distinguishable_and_convictable`.)

## Matching and exceeding buildr's bb engine

buildr's "bb engine" — the asset its fleet voted unanimously to keep — is an
append-only shared log + wake/spool/event-notify + receipt-identity. dregg has each
piece, in verified form:

| bb engine | dregg substrate |
|-----------|-----------------|
| append-only log | the blocklace (`blocklace/`) |
| spool / mailbox | `MessageRelay` per-recipient queue |
| wake / event-notify | `Waker` (cursor-advance is the wake) |
| receipt-identity | `CustodyReceipt` + the drain-witness (`Delivery`) |

Where dregg **exceeds** a plain bb engine — every delivery is a *cap-gated,
conserved, verifiable turn*:

1. **You cannot forge a wake.** A wake is minted only when a real enqueue advanced
   the monotone cursor. There is no public setter; a subscriber cannot fabricate a
   signal that work arrived. (Test: `wake_cannot_be_forged`.)
2. **A receipt is unforgeable.** Only the relay's Ed25519 key produces a verifying
   `CustodyReceipt` (EUF-CMA, via `ed25519-dalek`). A dropped delivery is
   convictable by the relay's own signature; an honest one is acquitted — the
   custody calculus mirrored from the verified Lean model `Dregg2.Exec.Custody`.
3. **Revocation / attenuation apply to channels.** A `SendCap` is an `AuthRequired`
   edge. It attenuates non-amplifyingly and revokes; an over-broad, mis-addressed,
   or revoked send is refused before anything is queued — no phantom work.
   (Tests: `over_attenuated_enqueue_refused_no_phantom_work`,
   `cap_attenuation_cannot_amplify`.)
4. **No claimed-but-undelivered ambiguity.** The receipt-identity section above —
   here it is cryptographic, not a convention an honest peer must uphold.

A plain bb engine asks you to *trust* that a spool entry's "done" bit was set
honestly. dregg makes "done" a content-addressed witness that only a real drain can
produce, and makes the absence of it convictable. That is the bb engine with its
one soft spot turned to stone.

## Grounding the Houyhnhnm IPC chapter

The data plane is the concrete realization of Houyhnhnm Computing's IPC chapter —
typed channels, implicit + explicit comms, protocols-as-meta-level:

- **Typed channels** — a `ChannelName` is a stable, named, cap-bearing edge. The
  type of the channel (who may send, with what attenuation, leaving what receipt) is
  carried by the `SendCap`, which is itself first-class data, not convention.
- **Implicit vs explicit comms** — a unicast `enqueue` is explicit point-to-point; a
  `publish` to a topic is the implicit, multi-cast meta-level. Both ride the same
  cap discipline, so a broadcast is governed exactly like a unicast.
- **Protocols as a meta-level** — because the cap *is* data, a protocol can be
  inspected, attenuated, handed off (via `crate::handoff`), and revoked at runtime.
  The "protocol" is not baked into the channel; it is the cap you hold over it.

## How ToolGateway-as-router rides on this

The sibling DP-1 lane turns `sdk/src/tool_gateway.rs` into a router. It does not need
its own transport: it *is* a `Bus` client. A tool call is an `enqueue` to the target
tool's inbox channel; the verdict/result is an `enqueue` back to the caller's reply
channel; the gateway's "fan a broadcast to all listening tools" is a `publish`. The
gateway gets receipt-identity for free — a tool call that was routed-but-never-handled
is structurally distinct from one that was handled, and the unhandled case is
convictable. The router owns *policy* (which caps to mint, which topics exist); the
data plane owns *mechanism* (enqueue / wake / drain / receipt).

## Status

- `captp/src/data_plane.rs` — the `Bus` and its types (`SendCap`, `Delivery`,
  `Waker`, `Wake`, `ChannelName`, `TopicName`, `DataPlaneError`), re-exported at the
  `dregg_captp` crate root.
- 9 tests covering the lifecycle (enqueue → wake → drain → witness), the
  receipt-identity both polarities (handled vs convictable-drop), pub/sub fan-out to
  N subscribers, the refused over-attenuated/revoked/mis-addressed enqueue (no
  phantom work), the non-amplifying cap algebra, and the unforgeable wake.
- Built on the existing `store_forward` (queue) + `custody` (receipt/witness)
  primitives; the blocklace remains the durable append-only spine beneath.
