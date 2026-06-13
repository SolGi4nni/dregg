# @dregg/sdk

TypeScript SDK for dregg. Two user-facing nouns and one shape:

```text
Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt
```

An unauthorized act is inexpressible on the public surface: every action
carries a real Ed25519 `Authorization::Signature` over the canonical
federation-bound signing message, and every submission rides a `SignedTurn`
envelope over the canonical `Turn::hash`. The raw vocabulary (including
unauthorized construction) is sealed behind `@dregg/sdk/raw`.

This package mirrors the Rust SDK (`sdk/`) shape-for-shape and
byte-for-byte: key derivation, postcard wire encoding, canonical hashes, and
signing preimages are differentially tested against the repo's own
`dregg-wasm` build, and the identity derivation is pinned by the same golden
vector as the Rust SDK, CLI, and browser extension — if any implementation
drifts, all of them fail together.

## Walkthrough (devnet)

```ts
import { AgentRuntime, Identity, NodeClient, ReceiptFilter, profiles } from "@dregg/sdk";

// 1. A named identity — the same $DREGG_HOME/profiles store as `dregg id`.
const identity = profiles.loadActive() ?? (profiles.create("me"), profiles.load("me"));

// 2. Bind to a node.
const node = new NodeClient("https://devnet.dregg.fg-goose.online", {
  devnetKey: process.env.DREGG_DEVNET_KEY, // the signed-turn ingress is operator-gated
});
const runtime = new AgentRuntime(identity, node);

// 3. Materialize + fund the agent cell (devnet faucet).
await runtime.faucet(2000);

// 4. Observe before acting.
const stream = node.events().subscribe(new ReceiptFilter().cell(identity.cellId()));

// 5. The one public turn shape.
const authorized = await runtime.turn().writeU64(0, 42n).fee(1000).sign();
console.log(authorized.explain()); // the anti-blind-signing reading, [sem]-tagged
const receipt = await authorized.submit();

// 6. The same noun arrives on the nervous system.
for await (const observed of stream) {
  if (observed.turnHash === receipt.turnHash) break;
}

// 7. The STARK attaches lazily (the node's async prove pool).
const proof = await node.turnProof(receipt.turnHash);
if (proof) receipt.attachProof(proof);
```

Runnable version: `node examples/devnet-walkthrough.mjs` (after `npm run build`).

## The organ nouns

Above the two base nouns sit the **organs** (`docs/ORGANS.md`) — the higher
primitives. Each is the ergonomic TS face of a node service: the node computes
the per-cell factory descriptors and seal fan-outs (Poseidon2 commitments,
X25519 key schedules) that the TS wire layer does not carry, and these clients
drive them. Every organ module documents an **Honest scope** for the
node-side/client-side line.

### Trustline — the bilateral line of credit (§1)

A line `issuer → holder` of N is an *attenuated capability whose exercise
debits a shared counter*; the executor-installed cell program enforces
`drawn ≤ ceiling` for life. Operator-gated (the node operator is the issuer).

```ts
const tl = runtime.trustline();
const line = await tl.open(holderCellHex, 1000n); // four-turn funded birth
await tl.draw(line.trustline, 250n);              // debit the shared counter (one-shot digest)
await tl.repay(line.trustline, 100n);             // restore the line
const pos = await tl.status(line.trustline);      // { line, drawn, remaining, escrow, open }
await tl.settle(line.trustline);                  // redeem outstanding to the holder
```

Runnable: `node examples/trustline.mjs`.

### Channels — the group-key epoch lift (§4)

A group is a cell; the membership root, key epoch, and key commitment live
on-cell. `remove(m)` darkens **both** m's forward-read ability and their
group-held capabilities in **one atomic epoch step** (the keystone — surfaced
as the `epochs_unified` invariant). Message bodies never touch the chain:
encrypt under the current epoch key client-side, post only ciphertext.

```ts
const ch = runtime.channels();
const g = await ch.create(7, [{ cell: aliceHex, sealPk: aliceSealHex }]);
await ch.join(g.channel, { cell: bobHex, sealPk: bobSealHex }); // → fresh sealed fan-out
await ch.post(g.channel, g.epoch, nonceHex, ciphertextHex);     // body, ciphertext only
await ch.remove(g.channel, bobHex);                             // bob darkened in ONE turn
for await (const m of ch.messages(g.channel)) { /* SSE delivery */ }
```

Runnable: `node examples/channel.mjs`.

### Mailbox — a hosted inbox over the relay (§2)

A store-and-forward inbox on the network-facing relay (its own port, default
`:3100`). Subscribe / drain are Ed25519-signed by the inbox owner (this client
signs them — differentially checked against the Rust signing path); sending is
open. The relay sees only ciphertext.

```ts
const mb = new MailboxClient("http://relay.example:3100", identity);
await mb.subscribe();                     // create your hosted inbox
// elsewhere: someone seals a body and POSTs it to your pubkey
const { messages } = await mb.drain(50);  // each carries a dequeue (custody) proof
```

Honest scope: sealing/opening (X25519 → ChaCha20-Poly1305) and re-running the
dequeue Merkle verifier are NOT done in pure TS — bring sealed ciphertext and
verify custody proofs via `@dregg/sdk/wasm` or the Rust SDK.

### Attested query — the light-client read surface (Noun 2's TS face)

The read-only twin: no identity, no signing. Fetch the federation-attested
state roots, finalized checkpoints, and a committed turn's full-turn STARK.

```ts
const aq = new AttestedQuery("https://devnet.dregg.fg-goose.online");
const roots = await aq.attestedRoots();        // federation-signed roots (+ signature count)
const cp = await aq.checkpoint();              // latest finalized checkpoint (+ qc votes)
const proof = await aq.turnProof(turnHashHex); // full-turn STARK BYTES
```

Honest scope: verifying a STARK or a threshold signature is a Rust/wasm
operation — pure TS surfaces the artifacts to verify elsewhere, it does not
return a checked verdict on its own.

Runnable: `node examples/attested-query.mjs`.

## Surface

| Export | Purpose |
|--------|---------|
| `Identity` | Ed25519 identity; `blake3 derive_key("dregg/0", seed64)` derivation |
| `profiles` | Shared `$DREGG_HOME/profiles` named-identity store (`dregg id …`) |
| `NodeClient` / `AgentRuntime` | A node's HTTP surface / an identity bound to it |
| `TurnBuilder` / `AuthorizedTurn` | Typed verbs → `.sign()` → `.submit()`; empty turns refused |
| `Receipt` / `TurnProof` | Proof-of-execution noun; STARK lazily attached, mis-bound attachments refused |
| `NodeEvents` / `ReceiptFilter` | `subscribe(filter)` → `AsyncIterable<Receipt>` (SSE, Last-Event-ID resume, reconnecting) |
| `explainTurn` / `renderTurn` / `explainAction` / `explainEffect` | The clerk's faithful reading: total, `[sem <digest>]`-tagged (equal text ⇒ equal semantics) |
| `program` | Cell-program atoms (`senderIs` / `senderInSlot` / `balanceGte` / `balanceLte` / `preimageGate`, `anyOf` / `not` / `implies`) + content-addressed factory descriptors |
| `TrustlineClient` | Organ §1 — `open` / `draw` / `repay` / `settle` / `close` / `status` (`runtime.trustline()`) |
| `ChannelsClient` | Organ §4 — `create` / `join` / `remove` / `rekey` / `post` / `status` / `messages` (`runtime.channels()`) |
| `MailboxClient` | Organ §2 — `subscribe` / `send` / `drain` / `unsubscribe` over the relay (owner-signed) |
| `AttestedQuery` | Light-client reads — `attestedRoots` / `checkpoint` / `turnProof` (no identity) |

### Turn verbs

`transfer(to, amount)` · `transferFrom(from, to, amount)` · `write(index, value)` ·
`writeU64(index, n)` · `grant(to, cap)` · `incrementNonce()` · `effect(e)` /
`effects(list)` · modifiers `on(target)` · `method(name)` · `fee(n)`.

Unlike the Rust in-process runtime there is no `.asCell(..)`: the remote
signed ingress pins `turn.agent` to the signer's default cell.

### Sealed: `@dregg/sdk/raw`

The wire vocabulary (postcard encoders, canonical hashes, signing preimages,
`unsignedAction`). Quarantined exactly like the Rust SDK's `sdk/src/raw.rs`:
if you import it in application code you are almost certainly building
something the executor will reject.

### Legacy: `@dregg/sdk/wasm`

The pre-refinement wasm-bound playground client (`DreggClient`,
`DreggRuntime`, proof/Merkle/Datalog toys) — unchanged, for existing
consumers.

## Building from a fresh clone

The package's core (`Identity` / turns / receipts / events / organs / program)
is **pure TypeScript** — no runtime wasm dependency. But the legacy
`@dregg/sdk/wasm` and `@dregg/sdk/browser` entry points, and the
differential-test oracle, import the repo's own `dregg-wasm` build
(`file:../wasm/pkg`, a dev/peer dependency). So a fresh clone must build that
package first, or the `.d.ts` emit step of `npm run build` fails with
`Cannot find module 'dregg-wasm'`:

```bash
# from the repo root — build the wasm package the SDK differentials against
(cd wasm && wasm-pack build --target web --out-dir pkg)
# then, in this package
cd sdk-ts && npm ci && npm run build
```

In Docker, mount the **repo root** (not just `sdk-ts/`) so the `../wasm/pkg`
path dependency resolves:

```bash
docker run --rm -v "$PWD":/repo -w /repo/sdk-ts node:22 \
  bash -c "npm ci && npm run build && npm test"
```

## Tests

```bash
npm test   # build + node --test  (needs ../wasm/pkg — see above)
```

- **Differential**: TS-built signed turns are byte-identical (postcard
  encoding AND canonical `Turn::hash` v3) to the Rust implementation via the
  repo's `dregg-wasm` build; BLAKE3 is differentially tested across chunk
  boundaries.
- **Golden vector**: seed `00..3f` → pubkey `335840a9…8b9a`, the same pin as
  `sdk/src/profiles.rs`, `cli/src/commands/id.rs`, and
  `extension/test/derivation.test.mjs`.
- Profile store, SSE resume/reconnect, explain totality + sem-tag
  discrimination, program content-addressing.

## License

AGPL-3.0-or-later
