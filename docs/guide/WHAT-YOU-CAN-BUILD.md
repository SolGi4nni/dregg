# What you can build

← [guide index](README.md) · [build with dregg](BUILD-WITH-DREGG.md)

A gallery of what dregg makes buildable, each entry anchored to a runnable
exemplar already in this tree. Every one rides the same verified executor and
leaves receipts; none is a separate stack. The recurring rule:
**the answer is never `Effect::FooApp`** — an app composes the generic verified
primitives.

## Verified service-cells

A cell that publishes a typed `InterfaceDescriptor` and dispatches methods through
`invoke()` — method membership decided by the same verified DFA router the
protocol uses, methods desugaring to ordinary effects. Three worked citizens:

### Key-value store — `starbridge-apps/kvstore/`

A verified, rollback-proof register store. Methods `put` / `delete` (signed,
replayable) and `get` (a serviced read — the named cross-cell-read seam). The
store's `CellProgram` scopes `StateConstraint::Monotonic` on the version slot to
the mutators, so a replayed or reordered mutation that would lower the version is
an **executor refusal on the verified commit path**, not a userspace check.

```sh
cargo test -p starbridge-kvstore
```

### Name registry — `starbridge-apps/nameservice/`

Per-name sovereign cells with ownership and rent: `register` / `renew` /
`transfer` / `revoke`, with `WriteOnce`/`Monotonic` slot caveats. A name is a
cell; its owner is whoever can produce its capability witness.

### Escrow market — `starbridge-apps/escrow-market/`

A four-stage market — `list` / `fund` / `ship` / `settle` — composed from generic
organs (a credit ceiling, sealed delivery, conservation, lifecycle state). The
resolve verbs are gated by the factory-installed cell program and proved on Lean
twins (`Dregg2.Apps.{EscrowFactory, ObligationFactory, BridgeCell}`).

More citizens live alongside these in `starbridge-apps/` (governed-namespace,
identity, subscription, bounty-board, sealed-auction, privacy-voting, …), each
factory-born and tested. See `starbridge-apps/README.md` and
[`docs/reference/services.md`](../reference/services.md).

## A reactive bot — `discord-bot/`

The clean exemplar of the `Reactor` pattern: a service that watches an on-chain
cell and reacts with its own receipted turn. The desktop submits a real dregg
turn to a command cell — the chain is the message bus — and the bot watches that
cell and reacts (`discord-bot/src/bot_reactor.rs`). A button press in the desktop
and a Discord slash command are two faces of one dregg-driven bot; the bot's
activity also surfaces as a live card (a `ViewNode`). See
[Build with dregg §2](BUILD-WITH-DREGG.md#2-reactor--watch-a-cell-react-with-a-turn).

## dregg in your Postgres — `pg-dregg/`

dregg's verified object-capability authorization as a PostgreSQL extension: the
same attenuable token that gates a dregg tool call also gates your SQL rows
through cap-secured row-level security — no amplification, offline verification,
and a hash-chain-verified store that refuses tampered or reordered batches.

```sql
CREATE EXTENSION pg_dregg;
ALTER SYSTEM SET dregg.issuer_pubkey = '…';

ALTER TABLE documents ENABLE ROW LEVEL SECURITY;
CREATE POLICY cap_read ON documents FOR SELECT
  USING (dregg_admits('read', id::text));

-- A reader presents an attenuated token; rows narrow to what the token admits.
SELECT set_config('dregg.token', 'dga1_…attenuated-to-public…', true);
SELECT id FROM documents;
```

The Postgres-free cores (capability decision, the predicate→jsonpath compiler,
the chain-verified store, the range-proof attester) run with plain `cargo`:

```sh
cargo run -p pg-dregg --example three_pillars   # cap-RLS · verified store · proof-attested ranges
```

The real SQL path needs PostgreSQL + `cargo-pgrx` (`pg-dregg/README.md`). The DX
vision is `docs/design-frontiers/PG-DREGG-DX.md`.

## Multiplayer / collaborative state — the membrane

A message in a chat can carry a **membrane**: a frustum-culled, cap-bounded
snapshot of a deos world-fork. A recipient rehydrates it, drives real turns on
their fork, and a **stitch** merges divergent forks back (a pushout, with
authority changes adjudicated at settlement). The cap algebra underneath is
`cell/src/membrane.rs` — a forwarded capability that exists only as the
conjunction of held caps and *cannot amplify* (it seals only if non-amplifying).
The wire shape and the world-fork flow are in `docs/deos/MEMBRANE-FORWARDER.md`
and `docs/deos/MEMBRANE-MERGE-SEAM.md`; the settlement guarantee is
`metatheory/Dregg2/Circuit/SettlementSoundness.lean`. See
[Build with dregg §3](BUILD-WITH-DREGG.md#3-membrane--composed-non-amplifying-authority).

## Collaborative documents with conflict objects — `dregg-doc/`

A Pijul-shaped document language: a document is a cell, an edit is a patch (a
turn), content is the fold of patch-history, and a **conflict is a first-class
object** — both alternatives held side-by-side, attributed, resolved by a later
patch you click, never a merge failure. The end-to-end offline-then-stitch walk:

```sh
cargo run -p dregg-doc --example two_device_offline_stitch
```

The north star is `docs/deos/DOCUMENT-LANGUAGE.md`. The same surface runs in a
browser tab — see [deos from the web](DEOS-FROM-THE-WEB.md) (`/doccollab.html`).

## Cap-secure authorization — macaroon ↔ cap

dregg's authority model is macaroon-style caveats welded to object capabilities,
enforced by the executor rather than by an out-of-band check:

- **Attenuated sub-agents.** `AgentRuntime::spawn_sub_agent` mints a fresh cell
  whose enforced credential grants exactly the allowed method verbs; a method
  outside the set is rejected with `TokenInsufficientCapability` at the executor
  (`sdk/src/runtime.rs`). A worked agent example is
  `cargo run -p dregg-sdk --example agent_demo`.
- **The tool gateway.** `tool_gateway::ToolGateway::invoke` turns an inbound
  untrusted tool-call into a cap-gated, metered, receipted delegated turn — or an
  in-band refusal. The rate ceiling is bound into the committed transition, so
  the executor rejects an over-rate write even if the in-band check is bypassed
  (`sdk/src/tool_gateway.rs`, the byte-faithful mirror of
  `Dregg2/Apps/ToolAccessDelegation.lean`).

The macaroon↔cap correspondence is the proven arrow
`chainGateG_implies_capAuthorityG` (`metatheory/.../CaveatCapBridge.lean`). See
[`docs/reference/auth.md`](../reference/auth.md).

## Agent-driven apps

The pieces above compose into apps an agent inhabits and drives: an agent holds a
cipherclerk, builds turns the same way you do, and every action it takes is a
cap-gated, receipted, light-client-verifiable fact. The SDK's sub-agent
delegation and the tool gateway are how you bound what an agent may do; the
reactor is how a service responds to one. The agent SDK surface is
[`docs/reference/sdk.md`](../reference/sdk.md).

## Embedding dregg in an existing service

If you want the kernel without its networking/consensus/storage,
`embed::DreggEngine` (`sdk/src/embed.rs`) is a zero-I/O, synchronous facade over
the turn executor and ledger: `execute_turn`, `validate_turn` (dry-run),
`prove_presentation` / `verify_presentation_*`, token mint/attenuate, and
state snapshot/load with an integrity hash. You handle transport and persistence.

## Where to go next

- The model and the turn flow these build on: [Build with dregg](BUILD-WITH-DREGG.md).
- The browser face of several of these (kvstore, doccollab, the inspector):
  [deos from the web](DEOS-FROM-THE-WEB.md).
