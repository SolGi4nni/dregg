# Getting started with DreggNet Cloud — first 5 minutes

The shortest path from "I just heard about this" to **a real, paid, verifiable
thing you did on the network**. Two routes: the **Discord bot** (for people) and
the **SDK** (for agents and builders). Pick one; both end at the same place — a
committed turn and a receipt you can verify yourself.

If you want the offer first (what DreggNet Cloud is, what you get, what you pay),
read [`DreggNet/docs/USING-DREGGNET.md`](../../DreggNet/docs/USING-DREGGNET.md).
If you want the model underneath (cell · turn · capability · receipt), read
[`docs/guide/`](guide/README.md). This page is just: *get to first value*.

> **Honest state (alpha).** DreggNet is an early devnet on subsidized/free
> compute. The one step that submits a turn to the live network needs the **edge
> node up**. It is currently being brought back online; the bot tells you if it's
> recovering and never loses your place, and the moment it's green the whole flow
> works. Everything before that step (your identity, your test DEC) is real and
> yours regardless. The local SDK/Hermes paths don't need the node at all.

---

## Route A — the Discord bot (for people, ~2 minutes)

The bot is the community front door. It maps Discord clicks to real dregg cells,
turns, and metered work on the live network. You learn **no commands** — you
click a guided tour.

1. **Join the server** and run **`/start`**.
2. Tap **Start the 2-minute tour**. It walks you through three steps, each a
   single button, ending with your receipt:
   - **Step 1 — Get my identity.** Mints a real dregg cell that's yours
     (custodial: the bot holds the key for convenience; `/cipherclerk export`
     hands it to you any time).
   - **Step 2 — Get test DEC.** The faucet grants test $DREGG (1000 DEC,
     subsidized, rate-limited to one claim/hour) so you can actually do something.
   - **Step 3 — Do one real thing.** Fires your **first real, paid, conserving
     turn**: a small payment to the DreggNet community cell, signed by your own
     key and verified by the node end-to-end (the same path `/send` uses). You get
     back a **receipt** (the turn hash), a link to see it on the explorer, and a
     link to **verify your own cell in your browser** on `portal.dregg.studio`
     (a wasm light client re-checks your history, trusting no server).
3. From there: tap **Claim my channel** and just **type**. Each message in your
   private channel becomes a cap-gated, metered, receipted Hermes turn under your
   own cell (`read <path>`, `search <query>`, `fetch <url>`, `run <cmd>`,
   `write <path>`, or plain chat through your own ported-in LLM key). This loop
   runs locally and works even while the node is recovering.

That's it. Everything else (balance, send, set your LLM key, the app dashboard)
is a button on `/start` or `/help`. The full map is
[`discord-bot/UX-REDESIGN.md`](../discord-bot/UX-REDESIGN.md).

---

## Route B — the SDK (for agents + builders, a few lines)

The SDK gives an agent the same lease / pay / run vocabulary programmatically.
The Rust core runs the **real verified executor in-process**, so identity and
your first metered turn work offline; paying a peer or running against the live
network is the same call pointed at a node.

### Python (`pip install dregg`)

```python
from dregg import ServiceRuntime

# 1. Identity — a real cell + a root capability you hold.
rt = ServiceRuntime.new("compute")

# 2. Fund / pay — one conserving Transfer (Σδ=0) over the Payable rail.
receipt = rt.pay_native(provider_cell, 1_000)

# 3. Run a metered, durable workload behind your capability.
lease = rt.lease(max_steps=8)
lease.fund(funder, 5_000)
step = lease.run(work)          # checkpoint += 1, metered, receipted

print(receipt.turn_hash.hex()) # your proof it committed
```

### TypeScript (`npm i @dregg/sdk`)

```ts
import { ServiceRuntime } from "@dregg/sdk";

const rt = await ServiceRuntime.create("compute");
const receipt = await rt.pay(provider, 1_000n, asset);   // conserving Transfer
const lease = await rt.execution.lease({ maxSteps: 8 });
const step = await lease.run(work);                      // metered, receipted
```

### Rust (`dregg-sdk`, the offline core)

The runnable end-to-end loop is
[`sdk/examples/agent_business_loop.rs`](../sdk/examples/agent_business_loop.rs):

```sh
cargo run -p dregg-sdk --example agent_business_loop
```

Then read, in order:

- [`docs/guide/AGENT-QUICKSTART.md`](guide/AGENT-QUICKSTART.md) — earn / spend /
  run in a few lines, what each call commits, how to read your receipts.
- [`docs/guide/SERVICE-ECONOMY-SDK.md`](guide/SERVICE-ECONOMY-SDK.md) — the full
  API surface, each call mapped to the underlying verified turn.

> The npm/PyPI packages publish from this repo's CI lanes. If a package isn't on
> the registry yet, build from the tree: `sdk-py/` (`maturin develop`) and
> `sdk-ts/` (`npm install && npm run build`) each have a README + `examples/`.

---

## What you get back, either route

A **`TurnReceipt`** — proof, not a log line:

```
turn_hash          content-address of the turn
pre_state_hash     state root before
post_state_hash    state root after
computrons_used    metered compute
agent              who authored it
previous_receipt_hash   the chain link to your prior turn
```

Your turns chain into a receipt chain, and anyone — including you, in your own
browser on the portal — can re-verify that chain against the network root without
trusting any server. That is the whole point: **don't trust, verify.**

---

## Where to go next

- The offer + the four things DreggNet Cloud does:
  [`DreggNet/docs/USING-DREGGNET.md`](../../DreggNet/docs/USING-DREGGNET.md).
- The model + your first app: [`docs/guide/`](guide/README.md) and the 15-minute
  all-local [`QUICKSTART.md`](../QUICKSTART.md).
- The one-doc orientation to what dregg *is*: [`docs/ONBOARDING.md`](ONBOARDING.md).

*Dated 2026-06-28. Verify against HEAD before relying on a specific value.*
</content>
