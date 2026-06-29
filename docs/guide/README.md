# Build-with-dregg — the developer guides

This is the developer onramp: the deeper guides a newcomer follows after the
landing page and the [15-minute hands-on quickstart](../../QUICKSTART.md). The
quickstart gets a node running and a real turn signed on `localhost`; these
guides explain the model, the build patterns, and the in-browser face.

Read in order, or jump to what you need:

1. **[Build with dregg](BUILD-WITH-DREGG.md)** — the model (cell · turn ·
   capability+caveat · receipt), your first app end-to-end against the SDK, and
   the core build patterns (service-cell, reactor, membrane, documents,
   cap-secure delegation), each with a real snippet.

2. **[What you can build](WHAT-YOU-CAN-BUILD.md)** — a gallery of capabilities,
   each anchored to a runnable exemplar in this tree: a verified KV store, a name
   registry, an escrow market, a reactive bot, dregg-in-Postgres, multiplayer
   world-forks, collaborative documents with conflict objects, and cap-secure
   authorization.

3. **[deos from the web](DEOS-FROM-THE-WEB.md)** — what deos is in a browser
   tab: card-worlds rendered from a renderer-independent view-tree, firing real
   verified turns over an in-tab executor with no node, and how to build a
   web-deos card-app.

4. **[Agent quickstart (for LLMs)](AGENT-QUICKSTART.md)** — you are an agent;
   here is how you earn, spend, and run on dregg in a few lines (pay → fund an
   execution lease → run a metered workload → pay-per-use through a gateway →
   read your receipts). Its full API surface + per-call → underlying-turn mapping
   is **[the service-economy SDK](SERVICE-ECONOMY-SDK.md)**; the runnable loop is
   [`sdk/examples/agent_business_loop.rs`](../../sdk/examples/agent_business_loop.rs).

## How these fit the rest of the tree

- The **one-sentence model** and the grounded what-is for every subsystem live in
  [`docs/OVERVIEW.md`](../OVERVIEW.md) and [`docs/reference/`](../reference/)
  (each reference is pinned to `file:line` at HEAD). When a guide and a reference
  disagree, the reference wins.
- The **author's developer manual** ([`docs/MANUAL/DEVELOPER.md`](../MANUAL/DEVELOPER.md))
  covers building the unified workspace and writing a deos-js program from a
  clean checkout. These guides are the task-oriented companion to it.
- The **SDK surfaces** are `sdk/` (Rust, the offline core), `sdk-py/` (Python),
  and `sdk-ts/` (TypeScript). Each ships its own README and an `examples/`
  directory; the guides point at the specific example files.
- **Running on the operated cloud** — these guides build against the substrate
  (a local node, the in-tab executor). To run metered workloads on the *operated*
  DreggNet cloud (the provider, the fly-compatible gateway, durable orchestration),
  the single developer hub is `DreggNet/docs/DEVELOPERS.md` — it cross-links back
  to these guides and walks the same identity → fund → lease → receipt loop
  against DreggNet's compute fleet.
